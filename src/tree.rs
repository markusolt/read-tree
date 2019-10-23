//! Necessary types for storing and interacting with trees.

#![deny(missing_docs)]

use std::fmt;

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
    /// [`pop`]: Sapling::pop
    /// [`push`]: Sapling::push
    MultipleRoots(Sapling<T>),
}

impl<T> fmt::Debug for BuildError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BuildError::Incomplete(_) => write!(f, "Incomplete"),
            BuildError::MultipleRoots(_) => write!(f, "MultipleRoots"),
        }
    }
}

impl<T> fmt::Display for BuildError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BuildError::Incomplete(_) => write!(f, "Incomplete tree structure"),
            BuildError::MultipleRoots(_) => write!(f, "Multiple roots in tree"),
        }
    }
}

impl<T> std::error::Error for BuildError<T> {}

/// An internal type that stores the payload and relationships of a node in a
/// [`Tree`]`<T>`.
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

/// A builder to construct [`Tree`]`<T>`s.
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

impl<T> Tree<T> {
    /// Returns the unique root node of the tree representing the entire tree.
    ///
    /// You can think of this as taking the complete slice of the tree similar
    /// to `&vec[..]` for a [`Vec`]`<T>`.
    pub fn root(&self) -> Node<'_, T> {
        Node {
            depth: 0,
            verts: &self.verts[..],
        }
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

/// A slice of a [`Tree`]`<T>`.
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
    depth: usize,
    verts: &'a [Vertex<T>],
}

impl<'a, T> Node<'a, T> {
    /// Returns a reference to the payload of the node.
    pub fn data(&self) -> &T {
        &self.verts[0].data
    }

    /// Returns the depth of the node within the tree. The root node returns
    /// depth `0`.
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// Returns the number of nodes within the subtree of this node.
    ///
    /// The count includes the node itself; a leaf node returns length `1`.
    pub fn len(&self) -> usize {
        self.verts.len()
    }

    /// Returns `true` if the node has no child nodes.
    pub fn is_leaf(&self) -> bool {
        self.verts.len() == 1
    }

    /// Returns a depth first iterator of nodes. It iterates all nodes in the
    /// subtree of the node, including the node itself. See [`Descendants`] for
    /// more information.
    pub fn iter(&self) -> Descendants<'a, T> {
        Descendants {
            depth: self.depth,
            verts: self.verts,
            pos: 0,
        }
    }

    /// Returns an iterator over the child nodes of the node. See [`Children`]
    /// for more information.
    pub fn children(&self) -> Children<'a, T> {
        Children {
            child_depth: self.depth + 1,
            verts: &self.verts[1..],
        }
    }

    /// Clones the subtree of the node into a new tree.
    ///
    /// Similar to [`push_node`] this operation is a lot cheaper if `T`
    /// implements [`Copy`]. It is internally based on
    /// [`Vec::extend_from_slice`].
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

/// A depth first iterator of [`Node`]`<T>`s. It iterates all nodes in a
/// subtree, including the root node.
///
/// # Examples
///
/// ```rust
/// use read_tree::Sapling;
///
/// let mut sap = Sapling::new();
/// sap.push(1);
/// sap.push_leaf(11);
/// sap.push(12);
/// sap.push_leaf(121);
/// sap.pop();
/// sap.pop();
/// let tree = sap.build().unwrap();
/// let mut iter = tree.root().iter();
///
/// assert_eq!(iter.next().unwrap().data(), &1);
/// assert_eq!(iter.next().unwrap().data(), &11);
/// assert_eq!(iter.next().unwrap().data(), &12);
/// assert_eq!(iter.next().unwrap().data(), &121);
/// assert!(iter.next().is_none());
/// ```
#[derive(Debug)]
pub struct Descendants<'a, T> {
    depth: usize,
    verts: &'a [Vertex<T>],
    pos: usize,
}

impl<'a, T> Iterator for Descendants<'a, T> {
    type Item = Node<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let verts = &self.verts[self.pos..self.pos + self.verts.get(self.pos)?.len + 1];

        let mut depth = self.depth;
        let mut i = 0;
        while i < self.pos {
            let len = self.verts[i].len;
            if i + len < self.pos {
                i += len + 1;
            } else {
                depth += 1;
                i += 1;
            }
        }

        self.pos += 1;
        Some(Node { depth, verts })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.verts.len(), Some(self.verts.len()))
    }

    fn count(self) -> usize {
        self.verts.len()
    }
}

/// An iterator of child nodes.
///
/// # Examples
///
/// ```rust
/// use read_tree::Sapling;
///
/// let mut sap = Sapling::new();
/// sap.push(1);
/// sap.push_leaf(11);
/// sap.push(12);
/// sap.push_leaf(121);
/// sap.pop();
/// sap.pop();
/// let tree = sap.build().unwrap();
/// let mut iter = tree.root().children();
///
/// assert_eq!(iter.next().unwrap().data(), &11);
/// assert_eq!(iter.next().unwrap().data(), &12);
/// assert!(iter.next().is_none());
/// ```
#[derive(Debug)]
pub struct Children<'a, T> {
    child_depth: usize,
    verts: &'a [Vertex<T>],
}

impl<'a, T> Iterator for Children<'a, T> {
    type Item = Node<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let (verts, remainder) = &self.verts.split_at(self.verts.get(0)?.len + 1);
        self.verts = remainder;
        Some(Node {
            depth: self.child_depth,
            verts,
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.verts.is_empty() {
            (0, Some(0))
        } else {
            (1, Some(self.verts.len()))
        }
    }
}
