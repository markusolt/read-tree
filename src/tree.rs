use crate::{Branch, BuildError, Children, ErrorWith, Node, ValidationError};
use std::convert::{TryFrom, TryInto};

/// An internal type that stores the payload and relationships of a [`Node`].
///
/// Every node on a tree is represented by a [`Vertex`]. The `len` field stores
/// the number of [`Descendants`] the node has. A leaf node has length `0`.
///
/// Every [`Tree`]`<T>` contains a [`Vec`]`<`[`Vertex`]`<T>>` representing the
/// nodes in a depth first order; meaning every vertex is followed by its first
/// child. This makes it very easy to take a slice of the vertex buffer that
/// represents a subtree.
///
/// The type implements [`Clone`] and [`Copy`] as long as the payload `T`
/// implements the same. Supporting [`Copy`] is important to ensure
/// [`Vec::extend_from_slice`] executes as fast as possible. This method is used
/// by [`Sapling::push_node`] to copy the subtree of a node into a sapling.
///
/// [`Descendants`]: crate::Descendants
/// [`Sapling::push_node`]: crate::Sapling::push_node
#[derive(Debug, Clone, Copy)]
pub struct Vertex<T> {
    pub data: T,
    pub len: usize,
}

impl<T> Vertex<T> {
    /// Returns a new vertex with payload `data` intending to own `len` many
    /// [`Descendants`].
    ///
    /// [`Descendants`]: crate::Descendants
    pub fn new(data: T, len: usize) -> Self {
        Vertex { data, len }
    }
}

/// Builder struct for [`Trees`][Tree].
///
/// Saplings allow easy creation of new trees. [`Nodes`][Node] are attached to
/// the tree one at a time until the tree is fully assembled. The sapling is
/// then converted into a tree using [`build`].
///
/// Internally a sapling pushes a [`Vertex`] on a
/// [`Vec`]`<`[`Vertex`]`<T>>` for each added node. It is possible to construct
/// such a `Vec` yourself. The `Vec` can then be converted into a tree using
/// [`Tree::from_vec`]. It is often easier to use the methods implemented for
/// saplings. Saplings also avoid the expensive validation caused by
/// [`Tree::from_vec`] by safely using the alternative
/// [`Tree::from_vec_unchecked`].
///
/// # Examples
///
/// We will construct a simple tree using a sapling.
///
/// ```rust
/// use read_tree::Sapling;
///
/// fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let mut sap = Sapling::new();
///
///     // Add the root node with payload `1`.
///     sap.push(1);
///
///     // Add child nodes to the root node.
///     sap.push_leaf(11);
///     sap.push(12);
///
///     // Add a child node to the selected node `12`.
///     sap.push_leaf(121);
///
///     // Close the selected node `12`.
///     sap.pop();
///
///     // Close the root node.
///     sap.pop();
///
///     // Build the sapling into a tree.
///     let _tree = sap.build()?;
///
///     Ok(())
/// }
/// ```
///
/// Alternatively we can create the tree without a sapling. The following
/// example constructs the same tree. The issue with this approach is
/// determining the correct `len` for every [`Vertex`], here the values are `[3,
/// 0, 1, 0]`. These values describe the number of [`Descendants`] the nodes
/// have. The root node has three descendants, the leaf nodes all have `0`.
///
/// ```rust
/// use read_tree::{Tree, Vertex};
///
/// fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let verts = vec![
///         Vertex::new(1, 3),
///         Vertex::new(11, 0),
///         Vertex::new(12, 1),
///         Vertex::new(121, 0),
///     ];
///     let _tree = Tree::from_vec(verts)?;
///
///     Ok(())
/// }
/// ```
///
/// [`build`]: Sapling::build
/// [`Descendants`]: crate::Descendants
#[derive(Debug, Clone)]
pub struct Sapling<T, ASM = ()> {
    open: Vec<(usize, ASM)>,
    verts: Vec<Vertex<T>>,
}

impl<T> Sapling<T> {
    pub fn new() -> Self {
        Sapling::new_asm()
    }

    pub fn with_capacity(len: usize, depth: Option<usize>) -> Self {
        Sapling::with_capacity_asm(len, depth)
    }
}

impl<T, ASM> Sapling<T, ASM> {
    pub fn new_asm() -> Self {
        Sapling {
            open: Vec::new(),
            verts: Vec::new(),
        }
    }

    pub fn with_capacity_asm(len: usize, depth: Option<usize>) -> Self {
        Sapling {
            open: Vec::with_capacity(depth.unwrap_or(0)),
            verts: Vec::with_capacity(len),
        }
    }

    /// Removes all [`Nodes`][Node] from the sapling.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let mut sap = Sapling::new();
    /// sap.push_leaf(());
    /// // [...]
    ///
    /// sap.clear();
    /// assert_eq!(sap.len(), 0);
    /// assert_eq!(sap.is_empty(), true);
    /// ```
    pub fn clear(&mut self) {
        self.open.clear();
        self.verts.clear();
    }

    /// Empties the sapling and changes its [`Assembly Information`] type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let mut sap: Sapling<(), usize> = Sapling::new_asm();
    /// sap.push_asm((), 4);
    /// assert_eq!(sap.peek_asm().unwrap().1, &4);
    ///
    /// let mut sap: Sapling<(), bool> = sap.clear_asm();
    /// assert!(sap.is_empty());
    /// ```
    ///
    /// [`Assembly Information`]: crate::vocab::AssemblyInformation
    pub fn clear_asm<ASM2>(mut self) -> Sapling<T, ASM2> {
        self.clear();

        Sapling {
            open: Vec::new(),
            verts: self.verts,
        }
    }

    /// Changes the saplings [`Assembly Information`] type. Resets the assembly
    /// information of all open nodes to `ASM::default()`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let mut sap: Sapling<(), usize> = Sapling::new_asm();
    /// sap.push_asm((), 4);
    /// assert_eq!(sap.peek_asm().unwrap().1, &4);
    ///
    /// let mut sap: Sapling<(), bool> = sap.with_asm_default();
    /// assert_eq!(sap.peek_asm().unwrap().1, &false);
    ///
    /// sap.pop();
    /// assert!(sap.build().is_ok());
    /// ```
    ///
    /// [`Assembly Information`]: crate::vocab::AssemblyInformation
    pub fn with_asm_default<ASM2>(self) -> Sapling<T, ASM2>
    where
        ASM2: Default,
    {
        Sapling {
            open: self
                .open
                .iter()
                .map(|(i, _)| (*i, ASM2::default()))
                .collect(),
            verts: self.verts,
        }
    }

    pub fn as_slice(&self) -> &[Vertex<T>] {
        &self.verts[..]
    }

    /// Returns the number of [`Nodes`][Node] in the sapling.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let mut sap = Sapling::new();
    /// assert_eq!(sap.len(), 0);
    ///
    /// sap.push_leaf(());
    /// sap.push(());
    /// sap.push_leaf(());
    /// sap.pop();
    /// assert_eq!(sap.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.verts.len()
    }

    /// Returns `true` if there are `0` [`Nodes`][Node] in the sapling.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let mut sap = Sapling::new();
    /// assert_eq!(sap.is_empty(), true);
    ///
    /// sap.push(());
    /// assert_eq!(sap.is_empty(), false);
    ///
    /// sap.pop();
    /// assert_eq!(sap.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.verts.is_empty()
    }

    /// Returns `true` if there are no open [`Nodes`][Node] in the sapling.
    ///
    /// Also returns `true` if the sapling is [`empty`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let mut sap = Sapling::new();
    /// assert_eq!(sap.is_complete(), true);
    ///
    /// sap.push_leaf(());
    /// assert_eq!(sap.is_complete(), true);
    ///
    /// sap.push(());
    /// assert_eq!(sap.is_complete(), false);
    ///
    /// sap.pop();
    /// assert_eq!(sap.is_complete(), true);
    /// ```
    ///
    /// [`empty`]: Sapling::is_empty
    pub fn is_complete(&self) -> bool {
        self.open.is_empty()
    }

    /// Returns `()` if the sapling can successfully be [`built`][build] into a
    /// [`Tree`].
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Sapling::build`].
    ///
    /// # Examples
    ///
    /// This method is useful for asserting a sapling can be built without
    /// consuming the sapling. The following example is somewhat contrived and
    /// should not be used.
    ///
    /// ```rust
    /// use read_tree::{Node, Sapling};
    ///
    /// let mut sap = Sapling::new();
    /// sap.push_leaf(());
    ///
    /// // `debug_assert!` will panic only during unoptimized builds. We use it
    /// // whenever we think the check will never fail, but want to be extra sure
    /// // without lowering performance in optimized builds.
    /// debug_assert!(sap.can_build().is_ok());
    ///
    /// // The following unsafe code is safe because `Sapling::can_build` ensures
    /// // the sapling contains a valid `Tree` and could be converted using
    /// // `Sapling::build`. We can now get a `Node` representing the tree in
    /// // `sap` without converting the sapling.
    /// let _node = unsafe { Node::from_slice_unchecked(sap.as_slice()) };
    /// ```
    ///
    /// The recommended way of doing the above would be the following. Notice
    /// that [`Sapling::build`] will perform some additional validations that
    /// the above code only performs in unoptimized builds.
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///     let mut sap = Sapling::new();
    ///     sap.push_leaf(());
    ///
    ///     let tree = sap.build()?;
    ///     let _node = tree.as_node();
    ///     sap = tree.into();
    ///
    ///     Ok(())
    /// }
    /// ```
    ///
    /// [build]: Sapling::build
    pub fn can_build(&self) -> Result<(), BuildError> {
        if self.is_empty() {
            return Err(BuildError::Empty);
        }
        if !self.is_complete() {
            return Err(BuildError::Incomplete);
        }
        if self.verts[0].len != self.verts.len() - 1 {
            return Err(BuildError::MultipleRoots);
        }

        Ok(())
    }

    /// Returns `()` if the sapling can successfully be
    /// [`built`][build_polytree] into a [`PolyTree`]. Similar to
    /// [`Sapling::can_build`].
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Sapling::build_polytree`].
    ///
    /// [build_polytree]: Sapling::build_polytree
    pub fn can_build_polytree(&self) -> Result<(), BuildError> {
        if self.is_empty() {
            return Err(BuildError::Empty);
        }
        if !self.is_complete() {
            return Err(BuildError::Incomplete);
        }

        Ok(())
    }

    pub fn push(&mut self, data: T)
    where
        ASM: Default,
    {
        self.push_asm(data, ASM::default());
    }

    pub fn push_asm(&mut self, data: T, asm: ASM) {
        self.open.push((self.verts.len(), asm));
        self.verts.push(Vertex::new(data, 0));
    }

    pub fn push_leaf(&mut self, data: T) {
        self.verts.push(Vertex::new(data, 0));
    }

    pub fn push_tree<ASM2>(&mut self, tree: Tree<T, ASM2>) -> Sapling<T, ASM2> {
        let mut sap = Sapling::from(tree);
        self.verts.append(&mut sap.verts);
        sap.clear();
        sap
    }

    pub fn push_polytree<ASM2>(&mut self, tree: PolyTree<T, ASM2>) -> Sapling<T, ASM2> {
        let mut sap = Sapling::from(tree);
        self.verts.append(&mut sap.verts);
        sap.clear();
        sap
    }

    pub fn push_node<'a>(&mut self, node: Node<'a, T>)
    where
        T: Clone,
    {
        self.verts.extend_from_slice(node.as_slice());
    }

    pub fn push_branch<'a>(&mut self, branch: Branch<'a, T>)
    where
        T: Clone,
    {
        self.verts.extend_from_slice(branch.as_slice());
    }

    pub fn peek(&self) -> Option<&T> {
        let (i, _) = self.open.last()?;

        Some(&self.verts[*i].data)
    }

    pub fn peek_asm(&self) -> Option<(&T, &ASM)> {
        let (i, asm) = self.open.last()?;

        Some((&self.verts[*i].data, asm))
    }

    pub fn peek_mut(&mut self) -> Option<&mut T> {
        let (i, _) = self.open.last_mut()?;

        Some(&mut self.verts[*i].data)
    }

    pub fn peek_asm_mut(&mut self) -> Option<(&mut T, &mut ASM)> {
        let (i, asm) = self.open.last_mut()?;

        Some((&mut self.verts[*i].data, asm))
    }

    pub fn pop(&mut self) -> Option<&mut T> {
        let (i, _) = self.open.pop()?;

        self.verts[i].len = self.verts.len() - i - 1;
        Some(&mut self.verts[i].data)
    }

    pub fn pop_asm(&mut self) -> Option<(&mut T, ASM)> {
        let (i, asm) = self.open.pop()?;

        self.verts[i].len = self.verts.len() - i - 1;
        Some((&mut self.verts[i].data, asm))
    }

    pub fn pop_as_leaf(&mut self) -> Option<&mut T> {
        let (i, _) = self.open.pop()?;

        Some(&mut self.verts[i].data)
    }

    pub fn pop_as_leaf_asm(&mut self) -> Option<(&mut T, ASM)> {
        let (i, asm) = self.open.pop()?;

        self.verts[i].len = self.verts.len() - i - 1;
        Some((&mut self.verts[i].data, asm))
    }

    /// Builds the sapling into a [`Tree`].
    ///
    /// The sapling is consumed in the process, trees however can easily be
    /// turned back into saplings.
    ///
    /// # Errors
    ///
    /// When the sapling does not fulfill all requirements of being a tree, a
    /// [`BuildError`] is returned. In case of an error the [`Result`] also
    /// carries the unchanged sapling. It can be retrieved from the error
    /// using [`ErrorWith::into_inner`]. There are three possible errors.
    ///
    /// 1. `Empty`
    ///
    ///    Trees must contain a root [`Node`]. Empty saplings can therefor not
    ///    be converted into trees.
    /// 2. `Incomplete`
    ///
    ///    The sapling is not allowed to contain open nodes. Ensure to [`pop`]
    ///    all nodes.
    /// 3. `MultipleRoots`
    ///
    ///    Trees must have exactly one root node. If the sapling has multiple
    ///    root nodes it must be converted into a [`PolyTree`] instead. See
    ///    [`build_polytree`].
    ///
    /// # Examples
    ///
    /// A simple sapling is successfully converted into a tree.
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///     let mut sap = Sapling::new();
    ///     sap.push_leaf(0);
    ///     let _tree = sap.build()?;
    ///
    ///     Ok(())
    /// }
    /// ```
    ///
    /// [`build_polytree`]: Sapling::build_polytree
    /// [`pop`]: Sapling::pop
    pub fn build(self) -> Result<Tree<T, ASM>, ErrorWith<BuildError, Self>> {
        self.try_into()
    }

    /// Builds the sapling into a [`PolyTree`].
    ///
    /// The sapling is consumed in the process, polytrees however can easily be
    /// turned back into saplings.
    ///
    /// # Errors
    ///
    /// When the sapling does not fulfill all requirements of being a polytree,
    /// a [`BuildError`] is returned. In case of an error the [`Result`]
    /// also carries the unchanged sapling. It can be retrieved
    /// from the error using [`ErrorWith::into_inner`]. There are two possible
    /// errors.
    ///
    /// 1. `Empty`
    ///
    ///    Polytrees must contain a root [`Node`]. Empty saplings can therefor
    ///    not be converted.
    /// 2. `Incomplete`
    ///
    ///    The sapling is not allowed to contain open nodes. Ensure to [`pop`]
    ///    all nodes.
    ///
    /// # Examples
    ///
    /// A simple sapling is successfully converted into a polytree.
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///     let mut sap = Sapling::new();
    ///     sap.push_leaf(0);
    ///     sap.push_leaf(1);
    ///     let _tree = sap.build_polytree()?;
    ///
    ///     Ok(())
    /// }
    /// ```
    ///
    /// [`pop`]: Sapling::pop
    pub fn build_polytree(self) -> Result<PolyTree<T, ASM>, ErrorWith<BuildError, Self>> {
        self.try_into()
    }
}

impl<T> Default for Sapling<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, ASM> From<Tree<T, ASM>> for Sapling<T, ASM> {
    fn from(tree: Tree<T, ASM>) -> Self {
        tree.sap
    }
}

impl<T, ASM> From<PolyTree<T, ASM>> for Sapling<T, ASM> {
    fn from(tree: PolyTree<T, ASM>) -> Self {
        tree.sap
    }
}

impl<'a, T> From<Node<'a, T>> for Sapling<T>
where
    T: Clone,
{
    fn from(node: Node<'a, T>) -> Self {
        let mut sap = Sapling::new();
        sap.push_node(node);
        sap
    }
}

#[derive(Debug, Clone)]
pub struct Tree<T, ASM = ()> {
    pub(crate) sap: Sapling<T, ASM>,
}

impl<T> Tree<T> {
    pub fn from_vec(
        vec: Vec<Vertex<T>>,
    ) -> Result<Self, ErrorWith<ValidationError, Vec<Vertex<T>>>> {
        vec.try_into()
    }

    pub unsafe fn from_vec_unchecked(vec: Vec<Vertex<T>>) -> Self {
        Tree {
            sap: Sapling {
                open: Vec::new(),
                verts: vec,
            },
        }
    }
}

impl<T, ASM> Tree<T, ASM> {
    pub fn as_node(&self) -> Node<T> {
        Node {
            index: 0,
            verts: self.as_slice(),
        }
    }

    pub fn as_slice(&self) -> &[Vertex<T>] {
        self.sap.as_slice()
    }

    pub fn len(&self) -> usize {
        self.sap.len()
    }

    pub fn get(&self, index: usize) -> Option<Node<T>> {
        if index >= self.sap.len() {
            return None;
        }

        Some(Node {
            index,
            verts: self.as_slice(),
        })
    }
}

impl<'a, T> From<Node<'a, T>> for Tree<T>
where
    T: Clone,
{
    fn from(node: Node<'a, T>) -> Self {
        let mut sap = Sapling::new();
        sap.push_node(node);
        Tree { sap }
    }
}

impl<T, ASM> TryFrom<Sapling<T, ASM>> for Tree<T, ASM> {
    type Error = ErrorWith<BuildError, Sapling<T, ASM>>;

    fn try_from(sap: Sapling<T, ASM>) -> Result<Self, Self::Error> {
        match sap.can_build() {
            Ok(_) => Ok(Tree { sap }),
            Err(err) => Err(ErrorWith::new(err, sap)),
        }
    }
}

impl<T, ASM> TryFrom<PolyTree<T, ASM>> for Tree<T, ASM> {
    type Error = ErrorWith<ValidationError, PolyTree<T, ASM>>;

    fn try_from(tree: PolyTree<T, ASM>) -> Result<Self, Self::Error> {
        if tree.as_slice()[0].len < tree.as_slice().len() - 1 {
            return Err(ErrorWith::new(ValidationError::MultipleRoots, tree));
        }

        Ok(Tree { sap: tree.sap })
    }
}

impl<T> TryFrom<Vec<Vertex<T>>> for Tree<T> {
    type Error = ErrorWith<ValidationError, Vec<Vertex<T>>>;

    fn try_from(vec: Vec<Vertex<T>>) -> Result<Self, Self::Error> {
        match Node::try_from(&vec[..]) {
            Ok(_) => Ok(unsafe { Tree::from_vec_unchecked(vec) }),
            Err(err) => Err(ErrorWith::new(err, vec)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PolyTree<T, ASM = ()> {
    pub(crate) sap: Sapling<T, ASM>,
}

impl<T> PolyTree<T> {
    pub fn from_vec(
        vec: Vec<Vertex<T>>,
    ) -> Result<Self, ErrorWith<ValidationError, Vec<Vertex<T>>>> {
        vec.try_into()
    }

    pub unsafe fn from_vec_unchecked(vec: Vec<Vertex<T>>) -> Self {
        PolyTree {
            sap: Sapling {
                open: Vec::new(),
                verts: vec,
            },
        }
    }
}

impl<T, ASM> PolyTree<T, ASM> {
    pub fn roots(&self) -> Children<T> {
        self.into()
    }

    pub fn as_slice(&self) -> &[Vertex<T>] {
        self.sap.as_slice()
    }

    pub fn len(&self) -> usize {
        self.sap.len()
    }

    pub fn get(&self, index: usize) -> Option<Node<T>> {
        if index >= self.sap.len() {
            return None;
        }

        Some(Node {
            index,
            verts: self.as_slice(),
        })
    }
}

impl<'a, T> From<Branch<'a, T>> for PolyTree<T>
where
    T: Clone,
{
    fn from(branch: Branch<'a, T>) -> Self {
        let mut sap = Sapling::new();
        sap.push_branch(branch);
        PolyTree { sap }
    }
}

impl<T, ASM> From<Tree<T, ASM>> for PolyTree<T, ASM> {
    fn from(tree: Tree<T, ASM>) -> Self {
        PolyTree { sap: tree.sap }
    }
}

impl<T, ASM> TryFrom<Sapling<T, ASM>> for PolyTree<T, ASM> {
    type Error = ErrorWith<BuildError, Sapling<T, ASM>>;

    fn try_from(sap: Sapling<T, ASM>) -> Result<Self, Self::Error> {
        match sap.can_build_polytree() {
            Ok(_) => Ok(PolyTree { sap }),
            Err(err) => Err(ErrorWith::new(err, sap)),
        }
    }
}

impl<T> TryFrom<Vec<Vertex<T>>> for PolyTree<T> {
    type Error = ErrorWith<ValidationError, Vec<Vertex<T>>>;

    fn try_from(vec: Vec<Vertex<T>>) -> Result<Self, Self::Error> {
        match Branch::try_from(&vec[..]) {
            Ok(_) => Ok(unsafe { PolyTree::from_vec_unchecked(vec) }),
            Err(err) => Err(ErrorWith::new(err, vec)),
        }
    }
}
