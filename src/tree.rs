//! Types for storing and exploring trees.

#![deny(missing_docs)]

/// An error returned when attempting to build a [`Sapling`]`<T>`.
///
/// The error contains the sapling that failed to build in order to return it to
/// the caller. Otherwise the [`build`] function would drop the sapling without
/// returning a resulting [`Tree`]`<T>`.
///
/// [`build`]: Sapling::build
pub enum BuildError<T> {
    /// The sapling is incomplete and not ready to be built.
    ///
    /// It is either empty or there are still unclosed nodes. Use [`pop_all`] to
    /// close any unclosed nodes and use [`is_empty`] to check if th sapling is
    /// empty.
    ///
    /// [`is_empty`]: Sapling::is_empty
    /// [`pop_all`]: Sapling::pop_all
    Incomplete(Sapling<T>),

    /// The sapling contains more than one root node.
    ///
    /// When creating nodes on a sapling it is possible to [`pop`] the root node
    /// and [`push`] a second root. Trees however must have a unique root.
    ///
    /// To get an iterator over the root nodes build the sapling into a
    /// [`PolyTree`]`<T>` using [`build_polytree`].
    ///
    /// [`build_polytree`]: Sapling::build_polytree
    /// [`pop`]: Sapling::pop
    /// [`push`]: Sapling::push
    MultipleRoots(Sapling<T>),
}

impl<T> std::fmt::Debug for BuildError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Incomplete(_) => write!(f, "Incomplete"),
            Self::MultipleRoots(_) => write!(f, "MultipleRoots"),
        }
    }
}

impl<T> std::fmt::Display for BuildError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Incomplete(_) => write!(f, "Incomplete tree structure"),
            Self::MultipleRoots(_) => write!(f, "Multiple roots in tree"),
        }
    }
}

impl<T> std::error::Error for BuildError<T> {}

/// An internal type that stores the payload and relationships of a node in a
/// [`Tree`]`<T>` or [`PolyTree`]`<T>`.
///
/// Every node on the tree is represented by a [`Vertex`]`<T>`. The `len` field
/// stores the number of descendants the node has; this is the number of nodes
/// in the subtree below the node. A leaf node has length `0`.
///
/// Every [`Tree`]`<T>` contains a [`Vec`]`<`[`Vertex`]`<T>>` representing the
/// trees nodes in a depth first order; meaning every vertex is followed by its
/// first child. This makes it very easy to take a slice of the vertex buffer
/// that represents a subtree. We expose such a slice to the user as a
/// [`Node`]`<T>`.
///
/// The type implements [`Clone`] and [`Copy`] as long as the payload `T`
/// implements the same. Supporting [`Copy`] is important to ensure
/// [`Vec::extend_from_slice`] executes as fast as possible. This method is used
/// by [`Sapling::push_tree`] to copy the nodes of a tree into another sapling.
#[derive(Debug, Clone, Copy)]
struct Vertex<T> {
    len: usize,
    data: T,
}

/// A builder to construct [`Tree`]`<T>`s and [`PolyTree`]`<T>`s.
///
/// Saplings are the only way of creating a [`Tree`]`<T>`. New saplings are
/// initialized empty, containing no nodes. Nodes are then added to the sapling
/// until the tree is complete. The sapling can then be turned into a tree.
///
/// Nodes are added to saplings using [`push`]. Adding a new node also selects
/// it, meaning later calls of [`push`] will attach the new node as a child to
/// this one. To close a node once all its child nodes have been added, call
/// [`pop`].
///
/// When the sapling is complete, turn it into a [`Tree`]`<T>` using [`build`].
/// This method returns a [`Result`]`<`[`Tree`]`<T>, `[`BuildError`]`<T>>` to
/// indicate if the sapling was built successfully. In case of an error
/// [`BuildError`]`<T>` will contain the sapling.
///
/// # Examples
///
/// ```rust
/// use read_tree::{Sapling, Tree};
///
/// fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let mut sap = Sapling::new();
///     assert!(sap.is_empty());
///
///     sap.push(1); // Add a new node to the tree carrying the payload `1`.
///     sap.push_leaf(11); // Add a child node to node `1`. This node will have no children.
///     sap.push(12); // Add another child node to `1`. Select this node.
///     sap.push_leaf(121); // Add leaf nodes to node `12`.
///     sap.push_leaf(122);
///
///     sap.pop(); // Close node `12`.
///     sap.pop(); // Close node `1`.
///
///     assert!(sap.is_ready());
///     let _tree = sap.build()?;
///
///     Ok(())
/// }
/// ```
///
/// [`build`]: Sapling::build
/// [`pop`]: Sapling::pop
/// [`push`]: Sapling::push
#[derive(Debug)]
pub struct Sapling<T> {
    path: Vec<usize>,
    verts: Vec<Vertex<T>>,
}

impl<T> Sapling<T> {
    /// Creates a new empty sapling.
    ///
    /// An empty sapling is not yet ready to be built. Add at least one node
    /// before building it into a tree.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let sap = Sapling::<usize>::new();
    /// assert!(sap.is_empty());
    /// assert!(sap.build().is_err());
    /// ```
    pub fn new() -> Self {
        Sapling {
            path: Vec::new(),
            verts: Vec::new(),
        }
    }

    /// Creates a new empty sapling with enough capacity to store `len` many
    /// nodes.
    ///
    /// The sapling is allowed to receive more than `len` nodes; this may
    /// however cause further memory allocations. For more information check out
    /// [`Vec::with_capacity`].
    ///
    /// The optional parameter `depth` should predict the maximum depth of the
    /// tree. If the depth is unknown use `None`. The depth should include the
    /// root node, can however exclude leaf nodes, if the leaf nodes will be
    /// added using [`push_leaf`]. The rule is that every call to [`push`]
    /// increases the depth, and every call to [`pop`] decreases it. Empty
    /// saplings start with depth `0` and methods like [`push_leaf`] do not
    /// affect the depth. If omitted `0` will be used by default.
    ///
    /// [`pop`]: Sapling::pop
    /// [`push_leaf`]: Sapling::push_leaf
    /// [`push`]: Sapling::push
    pub fn with_capacity(len: usize, depth: Option<usize>) -> Self {
        Sapling {
            path: Vec::with_capacity(depth.unwrap_or(0)),
            verts: Vec::with_capacity(len),
        }
    }

    /// Adds a new node with the payload `data` to the sapling.
    ///
    /// The new node is positioned as a child node of the currently selected
    /// node. The selected node will be changed to be the new node until the
    /// next call of [`pop`]. To avoid changing the selection use [`push_leaf`]
    /// instead; note that this will make it impossible to attach child nodes to
    /// the node, forcing it to be a leaf node.
    ///
    /// Nodes have to be added to the sapling in the correct oder. Once a node
    /// has been closed using [`pop`] its subtree is finalized and can no longer
    /// be changed.
    ///
    /// [`pop`]: Sapling::pop
    /// [`push_leaf`]: Sapling::push_leaf
    /// [`push`]: Sapling::push
    pub fn push(&mut self, data: T) {
        self.path.push(self.verts.len());
        self.verts.push(Vertex { len: 0, data });
    }

    /// Adds a new leaf node with the payload `data` to the sapling.
    ///
    /// This method is a convenient shortcut that behaves the same as calling
    /// [`push`] immediately followed by [`pop`].
    ///
    /// [`pop`]: Sapling::pop
    /// [`push`]: Sapling::push
    pub fn push_leaf(&mut self, data: T) {
        self.verts.push(Vertex { len: 0, data });
    }

    /// Adds another tree to the selected node in the sapling. This operation
    /// does not change the selected node, similar to [`push_leaf`].
    ///
    /// Empties `tree` in the process and returns it as an empty sapling. This
    /// allows the caller to reuse the trees internal buffers.
    ///
    /// [`push_leaf`]: Sapling::push_leaf
    pub fn push_tree(&mut self, tree: Tree<T>) -> Sapling<T> {
        let mut sap = tree.into_sapling();
        self.verts.append(&mut sap.verts);
        sap.clear();
        sap
    }

    /// Adds another poly-tree to the selected node in the sapling. This
    /// operation does not change the selected node, similar to [`push_leaf`].
    ///
    /// Empties `tree` in the process and returns it as an empty sapling. This
    /// allows the caller to reuse the trees internal buffers.
    ///
    /// [`push_leaf`]: Sapling::push_leaf
    pub fn push_polytree(&mut self, tree: PolyTree<T>) -> Sapling<T> {
        let mut sap = tree.into_sapling();
        self.verts.append(&mut sap.verts);
        sap.clear();
        sap
    }

    /// Clones the contents of a node and attaches the cloned subtree to the
    /// sapling. Requires the payload type `T` to be [`Clone`].
    ///
    /// If `T` implements [`Copy`], the cloning of the subtree is relatively
    /// cheap. See [`Vec::extend_from_slice`] for more information.
    pub fn push_node(&mut self, node: Node<T>)
    where
        T: Clone,
    {
        self.verts.extend_from_slice(node.verts);
    }

    /// Returns a reference to the payload of the selected node. Returns `None`
    /// if no node is currently selected; this happens when the sapling is empty
    /// or after a root node was closed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let mut sap = Sapling::new();
    /// sap.push(0);
    /// sap.push(1);
    ///
    /// assert_eq!(sap.peek(), Some(&1));
    /// assert_eq!(sap.pop(), Some(&1));
    ///
    /// assert_eq!(sap.peek(), Some(&0));
    /// assert_eq!(sap.pop(), Some(&0));
    ///
    /// assert_eq!(sap.peek(), None);
    /// assert_eq!(sap.pop(), None);
    /// ```
    pub fn peek(&self) -> Option<&T> {
        let i = *self.path.last()?;
        Some(&self.verts[i].data)
    }

    /// Closes the selected node.
    ///
    /// The subtree under the selected node is complete and will be closed. From
    /// then on new nodes will be attached to the parent of the closed node.
    ///
    /// Returns a reference to the payload of the closed node. Returns `None` if
    /// no node was selected; this happens when the sapling is empty or after a
    /// root node has been closed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let mut sap = Sapling::new();
    /// sap.push(0);
    /// assert_eq!(sap.pop(), Some(&0));
    ///
    /// assert!(sap.is_ready());
    /// ```
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let mut sap = Sapling::<usize>::new();
    /// assert_eq!(sap.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<&T> {
        let i = self.path.pop()?;
        self.verts[i].len = self.verts.len() - i - 1;
        Some(&self.verts[i].data)
    }

    /// Closes all open nodes.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let mut sap = Sapling::new();
    /// sap.push(0);
    /// sap.push(1);
    /// sap.push(2);
    /// sap.pop_all();
    ///
    /// assert!(sap.is_ready());
    /// ```
    pub fn pop_all(&mut self) {
        while let Some(i) = self.path.pop() {
            self.verts[i].len = self.verts.len() - i - 1;
        }
    }

    /// Closes the current node and makes it a leaf node.
    ///
    /// Any nodes that were attached to the node will be attached to its parent
    /// instead.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let mut sap = Sapling::new();
    /// sap.push(0);
    /// sap.push(1);
    /// sap.push_leaf(2);
    ///
    /// // make `1` a leaf node; changing `2` to be a child of `0`
    /// sap.pop_as_leaf();
    /// sap.pop();
    ///
    /// let tree = sap.build().unwrap();
    /// let mut iter = tree.root().children();
    ///
    /// assert_eq!(iter.next().unwrap().data(), &1);
    /// assert_eq!(iter.next().unwrap().data(), &2);
    /// assert!(iter.next().is_none());
    /// ```
    pub fn pop_as_leaf(&mut self) -> Option<&T> {
        let i = self.path.pop()?;
        Some(&self.verts[i].data)
    }

    /// Closes all open nodes and makes them all leaf nodes.
    ///
    /// If there are open nodes in the sapling, this will create multiple root
    /// nodes.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::{BuildError, Sapling};
    ///
    /// let mut sap = Sapling::new();
    /// sap.push(0);
    /// sap.push(1);
    ///
    /// sap.pop_as_leaf_all();
    /// match sap.build().unwrap_err() {
    ///     BuildError::MultipleRoots(_) => (),
    ///     _ => panic!(),
    /// }
    /// ```
    pub fn pop_as_leaf_all(&mut self) {
        self.path.clear();
    }

    /// Removes all nodes from the sapling, making it empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let mut sap = Sapling::new();
    /// sap.push_leaf(0);
    /// assert_eq!(sap.is_empty(), false);
    ///
    /// sap.clear();
    /// assert_eq!(sap.is_empty(), true);
    /// ```
    pub fn clear(&mut self) {
        self.path.clear();
        self.verts.clear();
    }

    /// Returns `true` if the sapling contains no nodes. Use [`push`] to add
    /// nodes.
    ///
    /// [`push`]: Sapling::push
    pub fn is_empty(&self) -> bool {
        self.verts.is_empty()
    }

    /// Return `true` if the sapling is ready to be built.
    ///
    /// Verifies that the sapling is not empty and has no open nodes. It does
    /// not verify the number of root nodes of the sapling. Building into a
    /// [`Tree`]`<T>` may still fail because trees do not allow multiple root
    /// nodes.
    pub fn is_ready(&self) -> bool {
        self.path.is_empty() && !self.verts.is_empty()
    }

    /// Builds the sapling into a [`Tree`]`<T>`.
    ///
    /// Consumes the sapling in the process. Fails when the sapling is
    /// incomplete or has multiple roots. When failing to build the sapling, the
    /// sapling is returned unmodified with the [`BuildError`]`<T>`.
    pub fn build(self) -> Result<Tree<T>, BuildError<T>> {
        if !self.is_ready() {
            return Err(BuildError::Incomplete(self));
        }
        if self.verts[0].len < self.verts.len() - 1 {
            return Err(BuildError::MultipleRoots(self));
        }

        Ok(Tree {
            path: self.path,
            verts: self.verts,
        })
    }

    /// Builds the sapling into a [`PolyTree`]`<T>`.
    ///
    /// Consumes the sapling in the process. Fails when the sapling is
    /// incomplete. When failing to build the sapling, the sapling is returned
    /// unmodified with the [`BuildError`]`<T>`.
    pub fn build_polytree(self) -> Result<PolyTree<T>, BuildError<T>> {
        if !self.is_ready() {
            return Err(BuildError::Incomplete(self));
        }

        Ok(PolyTree {
            path: self.path,
            verts: self.verts,
        })
    }
}

impl<T> Default for Sapling<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// A read-only tree data structure.
///
/// Trees are created from [`Sapling`]`<T>`s. Most interactions with trees
/// happen on slices of them called [`Node`]s. Get a node representing the
/// entire tree using [`root`].
///
/// [`root`]: Tree::root
#[derive(Debug)]
pub struct Tree<T> {
    path: Vec<usize>,
    verts: Vec<Vertex<T>>,
}

#[allow(clippy::len_without_is_empty)]
impl<T> Tree<T> {
    /// Returns the unique root node of the tree representing the entire tree.
    ///
    /// You can think of this as taking the complete slice of the tree similar
    /// to `&vec[..]` for a [`Vec`]`<T>`.
    pub fn root(&self) -> Node<T> {
        Node {
            rank: 0,
            verts: &self.verts[..],
        }
    }

    /// Returns the node with the specified `rank`.
    pub fn get(&self, rank: usize) -> Option<Node<T>> {
        if rank >= self.verts.len() {
            return None;
        }

        Some(Node {
            rank,
            verts: &self.verts[..],
        })
    }

    /// Returns the number of nodes in the tree.
    ///
    /// Because trees are required to have exactly one root node, the length
    /// will always be at least `1`.
    pub fn len(&self) -> usize {
        self.verts.len()
    }

    /// Turns the tree back into a sapling. No nodes are removed from the
    /// tree; building the returned sapling will result in the original tree.
    ///
    /// All internal buffers are reused, making this a cheap operation. The only
    /// cost of converting [`Sapling`]`<T>`s and [`Tree`]`<T>`s back and forth
    /// is the validation that occurs during [`build`].
    ///
    /// [`build`]: Sapling::build
    pub fn into_sapling(self) -> Sapling<T> {
        Sapling {
            path: self.path,
            verts: self.verts,
        }
    }
}

/// A read-only poly-tree data structure.
///
/// Similar to [`Tree`]`<T>` but allows multiple root nodes.
#[derive(Debug)]
pub struct PolyTree<T> {
    path: Vec<usize>,
    verts: Vec<Vertex<T>>,
}

#[allow(clippy::len_without_is_empty)]
impl<T> PolyTree<T> {
    /// Returns an iterator over the root nodes of the poly-tree.
    pub fn roots(&self) -> Children<T> {
        Children {
            top: 0,
            bottom: self.verts.len(),
            verts: &self.verts[..],
        }
    }

    /// Returns the node with the specified `rank`.
    pub fn get(&self, rank: usize) -> Option<Node<T>> {
        if rank >= self.verts.len() {
            return None;
        }

        Some(Node {
            rank,
            verts: &self.verts[..],
        })
    }

    /// Returns the number of nodes in the poly-tree.
    ///
    /// Because poly-trees are required to not be empty, the length will always
    /// be at least `1`.
    pub fn len(&self) -> usize {
        self.verts.len()
    }

    /// Turns the poly-tree back into a sapling. No nodes are removed from the
    /// tree; building the returned sapling will result in the original
    /// poly-tree.
    ///
    /// All internal buffers are reused, making this a cheap operation. The only
    /// cost of converting [`Sapling`]`<T>`s and [`PolyTree`]`<T>`s back and
    /// forth is the validation that occurs during [`build_polytree`].
    ///
    /// [`build_polytree`]: Sapling::build_polytree
    pub fn into_sapling(self) -> Sapling<T> {
        Sapling {
            path: self.path,
            verts: self.verts,
        }
    }
}

/// A slice of a [`Tree`]`<T>` or [`PolyTree`]`<T>`.
///
/// A node is essentially the same as a tree, except it does not own its data.
///
/// Navigating the subtree of a node is done using iterators.
///
/// *It is planned to add a query type that allows querying nodes from subtrees
/// using chains of conditions. Currently only some basic iterators are
/// available.*
#[derive(Debug)]
pub struct Node<'a, T> {
    rank: usize,
    verts: &'a [Vertex<T>],
}

impl<'a, T> Node<'a, T> {
    /// Returns a reference to the payload of the node.
    pub fn data(self) -> &'a T {
        &self.verts[self.rank].data
    }

    /// Returns the rank of the node in the tree. The rank can be used to look
    /// up the node from the tree using [`get`].
    ///
    /// The rank also exposes information about the structure of the tree. Any
    /// node `child` with a rank greater than that of a node `parent` but not
    /// exceeding `parent.rank() + parent.len()` is a descendant of `parent`.
    ///
    /// [`get`]: Tree::get
    pub fn rank(self) -> usize {
        self.rank
    }

    /// Returns the number of descending nodes within the subtree of this node.
    /// A leaf node returns length `0`.
    pub fn len(self) -> usize {
        self.verts[self.rank].len
    }

    /// Returns `true` if the node has no child nodes.
    pub fn is_empty(self) -> bool {
        self.verts[self.rank].len == 0
    }

    /// Returns the node with the specified `rank`.
    ///
    /// The rank must be relative to the trees root, or the most recently pruned
    /// node. See [`prune`] for more information.
    ///
    /// [`prune`]: Node::prune
    pub fn get(self, rank: usize) -> Option<Node<'a, T>> {
        if rank >= self.verts.len() {
            return None;
        }

        Some(Node {
            rank,
            verts: self.verts,
        })
    }

    /// Returns the parent of the node or `None` if it does not have one.
    pub fn parent(self) -> Option<Node<'a, T>> {
        self.ancestors().next()
    }

    /// Returns an iterator over the child nodes of the node. See [`Children`]
    /// for more information about the iterator.
    pub fn children(self) -> Children<'a, T> {
        Children::from(self)
    }

    /// Returns a depth first iterator of nodes. It iterates all nodes in the
    /// subtree of the node, including the node itself. See [`Descendants`] for
    /// more information about the iterator.
    pub fn descendants(self) -> Descendants<'a, T> {
        Descendants::from(self)
    }

    /// Returns an iterator over the parent nodes. The parent of the node is
    /// first. The root of the tree is last. See [`Ancestors`] for more
    /// information about the iterator.
    pub fn ancestors(self) -> Ancestors<'a, T> {
        Ancestors::from(self)
    }

    /// Returns the node isolated from the rest of the tree.
    ///
    /// A pruned node will always have rank `0`, and it will be impossible to
    /// access ancestors from it. It is still possible to explore the subtree
    /// below the node.
    ///
    /// When getting nodes by rank you must get them from this or any descending
    /// node. If you use the rank in a node that is not affected by this prune,
    /// it will return some other node. Think of the pruned node as an entirely
    /// new tree with its own ranks.
    pub fn prune(self) -> Node<'a, T> {
        Node {
            rank: 0,
            verts: &self.verts[self.rank..=self.rank + self.verts[self.rank].len],
        }
    }

    /// Clones the contents of the node into a new [`Tree`]`<T>`.
    ///
    /// Similar to [`push_node`] this operation is cheaper if `T` implements
    /// [`Copy`]. It is internally based on [`Vec::extend_from_slice`].
    ///
    /// [`push_node`]: Sapling::push_node
    pub fn into_tree(self) -> Tree<T>
    where
        T: Clone,
    {
        let mut verts = Vec::new();
        verts.extend_from_slice(self.verts);

        Tree {
            path: Vec::new(),
            verts,
        }
    }
}

impl<'a, T> Copy for Node<'a, T> {}

impl<'a, T> Clone for Node<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}

/// Iterates the children of a node.
///
/// # Examples
///
/// ```rust
/// use read_tree::Sapling;
///
/// fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let mut sap = Sapling::new();
///     sap.push(1);
///     sap.push_leaf(11);
///     sap.push(12);
///     sap.push_leaf(121);
///     sap.pop();
///     sap.pop();
///     let tree = sap.build()?;
///     let mut iter = tree.root().children();
///
///     assert_eq!(iter.next().unwrap().data(), &11);
///     assert_eq!(iter.next().unwrap().data(), &12);
///     assert!(iter.next().is_none());
///
///     Ok(())
/// }
/// ```
#[derive(Debug)]
pub struct Children<'a, T> {
    /// The next child node.
    top: usize,

    /// One beyond the last child node.
    bottom: usize,
    verts: &'a [Vertex<T>],
}

impl<'a, T> Children<'a, T> {
    /// Creates a new iterator over the children of a node.
    pub fn from(node: Node<'a, T>) -> Self {
        Children {
            top: node.rank() + 1,
            bottom: node.rank() + node.len() + 1,
            verts: node.verts,
        }
    }
}

impl<'a, T> Iterator for Children<'a, T> {
    type Item = Node<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.top >= self.bottom {
            return None;
        }

        let ret = Node {
            rank: self.top,
            verts: self.verts,
        };
        self.top += self.verts[self.top].len + 1;
        Some(ret)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.top >= self.bottom {
            (0, Some(0))
        } else {
            (1, Some(self.bottom - self.top))
        }
    }
}

/// Iterates all descendants of a node depth first.
///
/// The iterator implements [`ExactSizeIterator`] and [`DoubleEndedIterator`]
/// giving access to [`len`] and [`rev`]. It also has fast implementations for
/// [`nth`] and [`last`].
///
///
/// # Examples
///
/// ```rust
/// use read_tree::Sapling;
///
/// fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let mut sap = Sapling::new();
///     sap.push(1);
///     sap.push(11);
///     sap.push_leaf(111);
///     sap.pop();
///     sap.push(12);
///     sap.push_leaf(121);
///     sap.pop();
///     sap.pop();
///     let tree = sap.build()?;
///     let mut iter = tree.root().descendants();
///
///     assert_eq!(iter.len(), 4);
///     assert_eq!(iter.next().unwrap().data(), &11);
///     assert_eq!(iter.next().unwrap().data(), &111);
///     assert_eq!(iter.next().unwrap().data(), &12);
///     assert_eq!(iter.next().unwrap().data(), &121);
///     assert!(iter.next().is_none());
///
///     Ok(())
/// }
/// ```
///
/// [`last`]: Iterator::last
/// [`len`]: ExactSizeIterator::len
/// [`nth`]: Iterator::nth
/// [`rev`]: Iterator::rev
#[derive(Debug)]
pub struct Descendants<'a, T> {
    /// The next node to yield from the top.
    top: usize,

    /// The previously yielded node from the bottom
    bottom: usize,
    verts: &'a [Vertex<T>],
}

impl<'a, T> Descendants<'a, T> {
    /// Creates a new iterator over the descendants of a node.
    pub fn from(node: Node<'a, T>) -> Self {
        Descendants {
            top: node.rank() + 1,
            bottom: node.rank() + node.len() + 1,
            verts: node.verts,
        }
    }
}

impl<'a, T> Iterator for Descendants<'a, T> {
    type Item = Node<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.top >= self.bottom {
            return None;
        }

        let ret = Node {
            rank: self.top,
            verts: self.verts,
        };
        self.top += 1;
        Some(ret)
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.top += n;
        self.next()
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }

    fn count(self) -> usize {
        self.len()
    }
}

impl<'a, T> DoubleEndedIterator for Descendants<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.top >= self.bottom {
            return None;
        }

        self.bottom -= 1;
        Some(Node {
            rank: self.bottom,
            verts: self.verts,
        })
    }
}

impl<'a, T> ExactSizeIterator for Descendants<'a, T> {
    fn len(&self) -> usize {
        self.bottom - self.top
    }
}

/// Iterates all ancestors of a node starting with the parent of the node.
///
/// The iterator implements [`DoubleEndedIterator`], allowing it to be reversed
/// using [`rev`].
///
/// [`rev`]: Iterator::rev
#[derive(Debug)]
pub struct Ancestors<'a, T> {
    /// The next potential top most ancestor.
    top: usize,

    /// The previously found bottom most ancestor.
    bottom: usize,
    verts: &'a [Vertex<T>],
}

impl<'a, T> Ancestors<'a, T> {
    /// Creates a new iterator over the ancestors of a node.
    pub fn from(node: Node<'a, T>) -> Self {
        Ancestors {
            top: 0,
            bottom: node.rank(),
            verts: node.verts,
        }
    }
}

impl<'a, T> Iterator for Ancestors<'a, T> {
    type Item = Node<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.top >= self.bottom {
            return None;
        }

        for i in (self.top..self.bottom).rev() {
            if self.bottom <= i + self.verts[i].len {
                self.bottom = i;
                return Some(Node {
                    rank: i,
                    verts: self.verts,
                });
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.top - self.bottom))
    }

    fn count(self) -> usize {
        // The reverse direction of the iterator can skip subtrees and should therefor
        // be faster for most trees.
        self.rev().count()
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, T> DoubleEndedIterator for Ancestors<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let mut i = self.top;
        while i < self.bottom {
            let len = self.verts[i].len;
            if i + len < self.bottom {
                i += len + 1;
            } else {
                self.top = i + 1;
                return Some(Node {
                    rank: i,
                    verts: self.verts,
                });
            }
        }

        None
    }
}
