//! Necessary types for storing and interacting with trees.

#![deny(missing_docs)]

/// An error enum returned when attempting to build a [Sapling][Sapling].
#[derive(Debug)]
pub enum Error {
    /// The sapling is incomplete and not ready to be built.
    ///
    /// It is either empty or there are still unfinished nodes.
    Incomplete,

    /// The sapling contains more than one root node.
    ///
    /// When creating nodes on a sapling it is possible to `pop()` the root node
    /// and `push(_)` a second root. Trees however must have a unique root.
    MultipleRoots,
}

/// An internal struct that stores the payload and relationships of a node on a
/// tree.
///
/// Every node on the tree is represented by a vertex. The `len` field stores
/// the number of descendants the node has; this is the number of nodes in the
/// subtree below the node. A leaf node has length `0`.
#[derive(Debug, Clone, Copy)]
struct Vertex<T> {
    len: usize,
    data: T,
}

/// A builder to construct [Tree][Tree]s.
///
/// Saplings are the only way of creating trees. New saplings are initialized
/// empty, containing no nodes. Nodes are then added to the sapling until the
/// tree is complete. The sapling can then be turned into a tree.
///
/// Nodes are added to saplings using `.push(_)`. Adding a new node also selects
/// it, meaning later calls of `.push(_)` will attach the new node as a child to
/// this one. To close a node once all its child nodes have been added, call
/// `.pop()`. When adding a node that will not have any child nodes, use
/// `.push_leaf(_)`; this acts the same as `.push(_); .pop();`.
///
/// When the sapling is complete, turn it into a tree using `.build()`. This
/// function returns a `Result<_, _>` to indicate if the sapling was built
/// successfully. To check if a sapling is ready to be built call `.is_ready()`.
///
/// # Example
///
/// ```rust
/// let mut sap = read_tree::Sapling::new();
/// assert!(sap.is_empty());
///
/// sap.push(1); // Add a new node to the tree carrying the payload `1`.
/// sap.push_leaf(11); // Add a child node to node `1`. This node will have no children.
///
/// sap.push(12); // Add another child node to `1`. Select this node.
/// sap.push_leaf(121); // Add leaf nodes to node `12`.
/// sap.push_leaf(122);
///
/// sap.pop(); // Close node `12`.
/// sap.pop(); // Close node `1`.
///
/// assert!(sap.is_ready());
/// let _tree = sap.build().unwrap();
/// ```
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
    /// ```rust
    /// let sap = read_tree::Sapling::<usize>::new();
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
    /// however cause additional allocations.
    ///
    /// The optional parameter `depth` should predict the maximum depth of the
    /// tree. If the depth is unknown use `None`. The depth should include the
    /// root node, can however exclude leaf nodes, if the leaf nodes will be
    /// added using `.push_leaf(_)`. Essentially every call to `push(_)`
    /// increases the depth, and every call to `pop()` decreases it.
    pub fn with_capacity(len: usize, depth: Option<usize>) -> Self {
        Sapling {
            path: Vec::with_capacity(depth.unwrap_or(0)),
            verts: Vec::with_capacity(len),
        }
    }

    /// Adds a new node with the payload `data` to the sapling.
    ///
    /// Until `.pop()` is called new nodes will be attached to this new node. To
    /// avoid changing the selected node use `.push_leaf(_)` instead.
    ///
    /// Note that nodes have to be added to the sapling in the correct oder.
    /// Once a node has been closed using `.pop()` its subtree is finalized and
    /// can no longer be changed.
    pub fn push(&mut self, data: T) {
        self.path.push(self.verts.len());
        self.verts.push(Vertex { len: 0, data });
    }

    /// Adds a new leaf node with the payload `data` to the sapling.
    pub fn push_leaf(&mut self, data: T) {
        self.verts.push(Vertex { len: 0, data });
    }

    /// Adds another tree to the selected node in the sapling. Does not change
    /// the selected node, similar to `.push_leaf(_)`.
    ///
    /// Empties `tree` in the process and returns it as an empty sapling.
    pub fn push_tree(&mut self, tree: Tree<T>) -> Sapling<T> {
        let mut sap = tree.into_sapling();
        self.verts.append(&mut sap.verts);
        sap.clear();
        sap
    }

    /// Closes the current node.
    ///
    /// The subtree under the current node is complete and will be closed. From
    /// now on new nodes will be attached to the parent of the closed node.
    ///
    /// Returns a reference to the payload of the closed node. Returns `None` if
    /// no node is currently selected; this happens when the sapling is empty or
    /// after a root node was closed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut sap = read_tree::Sapling::new();
    /// sap.push(0);
    /// sap.pop();
    /// sap.build().unwrap();
    /// ```
    ///
    /// ```rust
    /// let mut sap = read_tree::Sapling::<usize>::new();
    /// assert!(sap.pop().is_none());
    /// ```
    ///
    /// ```rust
    /// let mut sap = read_tree::Sapling::new();
    /// sap.push_leaf(0);
    /// assert!(sap.pop().is_none());
    /// ```
    pub fn pop(&mut self) -> Option<&T> {
        let i = self.path.pop()?;
        self.verts[i].len = self.verts.len() - i - 1;
        Some(&self.verts[i].data)
    }

    /// Removes all nodes from the sapling, making it empty.
    ///
    /// # Example
    ///
    /// ```rust
    /// let mut sap = read_tree::Sapling::new();
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

    /// Returns `true` if the sapling contains no nodes. Use `push(_)` to add
    /// nodes.
    pub fn is_empty(&self) -> bool {
        self.verts.is_empty()
    }

    /// Return `true` if the sapling is ready to be built.
    ///
    /// Verifies that the sapling is not empty and has no open nodes. It does
    /// not verify the number of root nodes of the sapling. Building into a
    /// [Tree][Tree] may still fail because trees do not allow multiple root
    /// nodes.
    pub fn is_ready(&self) -> bool {
        self.path.is_empty() && !self.verts.is_empty()
    }

    /// Builds the sapling into a tree.
    ///
    /// Consumes the sapling in the process. Fails when the sapling is
    /// incomplete or has multiple roots. When failing to build the sapling, the
    /// sapling is returned unmodified with the error.
    pub fn build(self) -> Result<Tree<T>, (Sapling<T>, Error)> {
        if !self.is_ready() {
            return Err((self, Error::Incomplete));
        }
        if self.verts[0].len < self.verts.len() - 1 {
            return Err((self, Error::MultipleRoots));
        }

        Ok(Tree {
            path: self.path,
            verts: self.verts,
        })
    }
}

impl<T: Clone> Sapling<T> {
    /// Clones the contents of a node and attaches the cloned subtree to the
    /// sapling.
    ///
    /// This is a relatively expensive step. The tree that `node` references is
    /// unaffected.
    pub fn push_node(&mut self, node: Node<T>) {
        self.verts.extend_from_slice(node.verts);
    }
}

/// A read-only tree data structure.
///
/// Trees are created by [Sapling][Sapling]s. Most interactions with trees
/// happen on slices of them called [Node][Node]s. Get a node representing the
/// entire tree using `.root()`.
#[derive(Debug)]
pub struct Tree<T> {
    path: Vec<usize>,
    verts: Vec<Vertex<T>>,
}

impl<T> Tree<T> {
    /// Returns the unique root node of the tree representing the entire tree.
    ///
    /// You can think of this as taking the complete slice of the tree similar
    /// to `&vec[..]` for a [Vec][std::vec::Vec].
    pub fn root(&self) -> Node<'_, T> {
        Node {
            depth: 0,
            verts: &self.verts[..],
        }
    }

    /// Returns the number of nodes in the tree.
    pub fn len(&self) -> usize {
        self.verts.len()
    }

    /// Turns the tree back into a sapling. No nodes are removed from the
    /// tree; building the returned sapling will result in an equivalent tree.
    pub fn into_sapling(self) -> Sapling<T> {
        Sapling {
            path: self.path,
            verts: self.verts,
        }
    }
}

/// A slice of a [Tree][Tree].
///
/// A node is essentially the same as a tree, only that it does not own its
/// data. You can navigate a node using iterators.
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
    /// subtree of the node, including the node itself. See
    /// [Descendants][Descendants] for more information.
    pub fn iter(&self) -> Descendants<'a, T> {
        Descendants {
            depth: self.depth,
            verts: self.verts,
            pos: 0,
        }
    }

    /// Returns an iterator over the child nodes of the node. See
    /// [Children][Children] for more information.
    pub fn children(&self) -> Children<'a, T> {
        Children {
            child_depth: self.depth + 1,
            verts: &self.verts[1..],
        }
    }
}

impl<'a, T: Clone> Node<'a, T> {
    /// Clones the subtree of the node into a new tree.
    ///
    /// This step may be expensive and should be avoided if possible.
    pub fn into_tree(self) -> Tree<T> {
        let mut verts = Vec::new();
        verts.extend_from_slice(self.verts);

        Tree {
            path: Vec::new(),
            verts,
        }
    }
}

/// A depth first iterator of nodes. It iterates all nodes in the subtree of the
/// node, including the node itself.
///
/// # Example
///
/// ```rust
/// let mut sap = read_tree::Sapling::new();
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
/// # Example
///
/// ```rust
/// let mut sap = read_tree::Sapling::new();
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
