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
    /// When creating nodes on a sapling it is possible to `pop()` the rootnode
    /// and `push(_)` a second one. Trees however must have a unique root. Use
    /// `build_polytree()` to build a [PolyTree][PolyTree].
    MultipleRoots,
}

/// An internal struct that stores the payload and structure of a tree.
///
/// Every node on the tree is represented by a vertex. The `len` field stores
/// the number of descendants the node has; this is the number of nodes in the
/// subtree below the node. A leaf node has length `0`.
#[derive(Debug)]
struct Vertex<T> {
    len: usize,
    data: T,
}

/// A builder to construct [Tree][Tree]s and [PolyTree][PolyTree]s.
///
/// Saplings are the only way of creating trees or poly-trees. New saplings are
/// initialized empty, containing no nodes. Nodes are then added to the sapling
/// until the tree is complete. The sapling can then be turned into a tree or a
/// poly-tree.
///
/// Nodes are added to saplings using `.push(_)`. Adding a new node also selects
/// it, meaning later calls of `push(_)` will attach the node as a child to this
/// one. To close a node once all child nodes were added call `pop()`. When
/// adding a node that should not have any child nodes, called leaf node, use
/// `.push_leaf(_)`. This function acts the same as `.push(_); .pop();`.
///
/// When the sapling is complete turn it into a tree or a poly-tree using
/// `.build()` or `.build_polytree()`. These functions return a `Result<_, _>`
/// to indicate if the sapling was ready. To check if a sapling is ready to be
/// built call `.is_ready()`.
///
/// # Example
///
/// ```rust
/// let mut sap = read_tree::Sapling::new();
///
/// sap.push(1); // Add a new node to the tree carrying the payload `1`.
/// sap.push_leaf(11); // Add a child node to node `1`. This node will have no children.
///
/// sap.push(12); // Add another child node to `1`.
/// sap.push_leaf(121); // Add leaf nodes to node `12`.
/// sap.push_leaf(122);
///
/// sap.pop(); // Close node `12`.
/// sap.pop(); // Close node `1`.
///
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
    /// sap.build().unwrap_err();
    /// ```
    pub fn new() -> Self {
        Sapling {
            path: Vec::new(),
            verts: Vec::new(),
        }
    }

    /// Adds a new node with the payload `data` to the sapling.
    ///
    /// Until `.pop()` is called new nodes will be attached to this new node. To
    /// avoid changing the selected node use `push_leaf(_)` instead.
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

    /// Finalizes the current node.
    ///
    /// The subtree under the current node is complete and will be sealed. From
    /// now on new nodes will be attached to the parent of the finalized node.
    ///
    /// Returns `None` if no node is currently selected. This happens when the
    /// sapling is empty or after a root node was finalized.
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
    pub fn pop(&mut self) -> Option<()> {
        let i = self.path.pop()?;
        self.verts[i].len = self.verts.len() - i - 1;
        Some(())
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
    /// incomplete or has multiple roots.
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

    /// Builds the sapling into a tree with multiple root nodes.
    ///
    /// Consumes the sapling in the process. Fails when the sapling is
    /// incomplete.
    pub fn build_polytree(self) -> Result<PolyTree<T>, (Sapling<T>, Error)> {
        if !self.is_ready() {
            return Err((self, Error::Incomplete));
        }

        Ok(PolyTree {
            path: self.path,
            verts: self.verts,
        })
    }
}

/// A read-only tree data structure.
///
/// Trees are created by [Sapling][Sapling]s. Most interactions with trees
/// happen on slices of them called [Node][Node]s.
#[derive(Debug)]
pub struct Tree<T> {
    path: Vec<usize>,
    verts: Vec<Vertex<T>>,
}

impl<T> Tree<T> {
    /// Returns the unique root node of the tree representing the entire tree.
    ///
    /// You can think of this as taking the complete slice of the tree similar
    /// to `&vec[..]` for a [Vec][std::vec::Vec] `vec`.
    pub fn root(&self) -> Node<'_, T> {
        Node {
            depth: 0,
            verts: &self.verts[..],
        }
    }

    /// Turns the tree back into a `Sapling`. No nodes are removed from the
    /// tree; building the returned sapling will result in an equivalent tree.
    pub fn into_sapling(self) -> Sapling<T> {
        Sapling {
            path: self.path,
            verts: self.verts,
        }
    }
}

/// A read-only tree data structure with multiple root nodes.
///
/// Similar to [Tree][Tree], but does not necessarily have a unique root node.
#[derive(Debug)]
pub struct PolyTree<T> {
    path: Vec<usize>,
    verts: Vec<Vertex<T>>,
}

impl<T> PolyTree<T> {
    /// Returns an iterator over the root nodes of the poly-tree.
    pub fn roots(&self) -> Children<'_, T> {
        Children {
            child_depth: 0,
            verts: &self.verts[..],
        }
    }

    /// Turns the poly-tree back into a `Sapling`. No nodes are removed from the
    /// tree; building the returned sapling will result in an equivalent
    /// poly-tree.
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
    /// Returns the depth of the node within the tree.
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// Returns a reference to the payload of the node.
    pub fn data(&self) -> &T {
        &self.verts[0].data
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

        let verts = &self.verts[self.pos..self.pos + self.verts.get(self.pos)?.len + 1];
        self.pos += 1;

        Some(Node { depth, verts })
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
}

#[cfg(test)]
mod test_sapling {
    use super::*;

    fn tiny() -> Tree<usize> {
        let mut sap = Sapling::new();
        sap.push_leaf(1);
        sap.build().unwrap()
    }

    fn small() -> Tree<usize> {
        let mut sap = Sapling::new();
        sap.push(1);
        sap.push_leaf(11);
        sap.push(12);
        sap.push(121);
        sap.push_leaf(1211);
        sap.pop();
        sap.push_leaf(122);
        sap.pop();
        sap.pop();
        sap.build().unwrap()
    }

    #[test]
    fn test_tiny() {
        tiny();
    }

    #[test]
    fn test_small() {
        small();
    }

    #[test]
    fn test_err() {
        let sap = Sapling::<usize>::new();
        sap.build().unwrap_err();

        let mut sap = Sapling::<usize>::new();
        assert!(sap.pop().is_none());

        let mut sap = Sapling::new();
        sap.push(0);
        sap.build().unwrap_err();

        let mut sap = Sapling::new();
        sap.push_leaf(0);
        sap.push_leaf(0);
        sap.build().unwrap_err();

        let mut sap = Sapling::new();
        sap.push(0);
        sap.push(0);
        sap.pop();
        sap.build().unwrap_err();
    }

    #[test]
    fn test_clear() {
        let mut sap = Sapling::new();
        sap.push_leaf(0);
        sap.clear();
        sap.build().unwrap_err();

        let mut sap = Sapling::new();
        sap.push(0);
        sap.clear();
        sap.push_leaf(0);
        sap.build().unwrap();

        let mut sap = Sapling::new();
        sap.push_leaf(0);
        sap.clear();
        sap.push_leaf(0);
        sap.build().unwrap();
    }

    #[test]
    fn test_iter_children() {
        let tree = small();
        let mut iter = tree.root().children();

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 1);
        assert_eq!(node.data(), &11);

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 1);
        assert_eq!(node.data(), &12);

        assert!(iter.next().is_none());
    }

    #[test]
    fn test_iter_descendants() {
        let tree = small();
        let mut iter = tree.root().iter();

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 0);
        assert_eq!(node.data(), &1);

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 1);
        assert_eq!(node.data(), &11);

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 1);
        assert_eq!(node.data(), &12);

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 2);
        assert_eq!(node.data(), &121);

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 3);
        assert_eq!(node.data(), &1211);

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 2);
        assert_eq!(node.data(), &122);

        assert!(iter.next().is_none());
    }
}