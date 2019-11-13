use crate::{BuildError, ErrorWith, Node, PolyTree, Tree, Vertex};
use std::convert::TryInto;

/// Builder struct for [`Trees`].
///
/// Saplings allow easy creation of new trees. [`Nodes`] are attached to the
/// tree one at a time until the tree is fully assembled. The sapling is then
/// converted into a [`Tree`] using [`build`].
///
/// Internally a sapling pushes a [`Vertex`] on a
/// [`Vec`]`<`[`Vertex`]`<T>>` for each added node. It is possible to construct
/// such a `Vec` yourself. The `Vec` can then be converted into a tree using
/// [`Tree::from_vec`]. It is often easier to use the methods implemented for
/// saplings. Saplings also avoid the expensive validation caused by
/// [`Tree::from_vec`].
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
/// Alternatively we could try creating the tree ourselves. This example
/// construct the same tree. The issue with this approach is determining the
/// correct `len` for every [`Vertex`], here the values are `[3, 0, 1, 0]`.
/// These values describe the number of [`Descendants`] the nodes have. The root
/// node has three descendants, the leaf nodes all have `0`.
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
/// [`Nodes`]: Node
/// [`Trees`]: Tree
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

    /// Removes all nodes from the sapling.
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

    pub fn verts(&self) -> &[Vertex<T>] {
        &self.verts[..]
    }

    /// Returns the number of nodes in the sapling.
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

    /// Returns `true` if there are `0` nodes in the sapling.
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

    /// Returns `true` if there are no open nodes in the sapling.
    ///
    /// Also returns `true` if the sapling is [`empty`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::Sapling;;
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

    pub fn can_build(&self) -> Result<(), BuildError> {
        if self.is_empty() {
            return Err(BuildError::Empty);
        }
        if !self.is_complete() {
            return Err(BuildError::Incomplete);
        }
        if self.verts()[0].len != self.verts().len() - 1 {
            return Err(BuildError::MultipleRoots);
        }

        Ok(())
    }

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
        self.verts.extend_from_slice(node.verts());
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
    /// turned back into a sapling.
    ///
    /// # Errors
    ///
    /// When the sapling does not fullfill all requirements of being a tree, a
    /// [`BuildError`] is returned. In case of an error the [`Result`] also
    /// carries the unchanged sapling. It can be retrieved from the error
    /// using [`ErrorWith::into_inner`]. There are three possible errors.
    ///
    /// 1. `Empty`
    ///
    ///    Trees must contain a root node. Empty saplings can therefor not be
    ///    converted into a tree.
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
    /// turned back into a sapling.
    ///
    /// # Errors
    ///
    /// When the sapling does not fullfill all requirements of being a
    /// polytree, a [`BuildError`] is returned. In case of an error the
    /// [`Result`] also carries the unchanged sapling. It can be retrieved
    /// from the error using [`ErrorWith::into_inner`]. There are two possible
    /// errors.
    ///
    /// 1. `Empty`
    ///
    ///    Polytrees must contain a root node. Empty saplings can therefor not
    /// be    converted.
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
