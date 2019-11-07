//! Definitions of common vocabulary.

use crate::Node;

/// The range of [`Indices`] of a [`Node`] and its [`Descendants`].
///
/// The scope of a node is the inclusive range `self.index()..=self.index() +
/// self.len()`.
///
/// Because of the internal ordering of indices, nodes with an index within this
/// range are either the node itself or a descendant of the node.
///
/// # Examples
///
/// We use the tree from [`small_tree`] to show some interesting scopes. Leaf
/// nodes always have a scope of length `1` and a [`Tree`]s root node always has
/// scope `0..tree.len()`.
///
/// ```rust
/// let tree = read_tree::demo::small_tree();
///
/// // The node with index `1` is a leaf node.
/// // Its scope is `1..=1`.
/// assert_eq!(tree.get(1).unwrap().scope(), 1..=1);
///
/// // The node with index `2` contains a large subtree.
/// // The last descendant has index `7`.
/// assert_eq!(tree.get(2).unwrap().scope(), 2..=7);
///
/// // The trees root node always spans the entire tree `0..tree.len()`.
/// assert_eq!(tree.as_node().scope(), 0..=tree.len() - 1);
/// ```
///
/// [`Descendants`]: crate::Descendants
/// [`Indices`]: Index
/// [`Node`]: crate::Node
/// [`small_tree`]: crate::demo::small_tree
/// [`Tree`]: crate::Tree
#[derive(Debug, Clone, Copy)]
pub struct Scope {
    /// Represents an inclusive range.
    pub range: (usize, usize),
}

impl Scope {
    pub fn as_range(self) -> std::ops::RangeInclusive<usize> {
        self.range.0..=self.range.1
    }
}

impl<'a, T> From<Node<'a, T>> for Scope {
    fn from(node: Node<T>) -> Self {
        Scope {
            range: node.scope().into_inner(),
        }
    }
}

/// The index of a [`Node`] in a [`Tree`].
///
/// The index of a node uniquely identifies it within its tree. To get the node
/// with a specific index from a tree use [`Tree::get`].
///
/// Indices can also be looked up on a node using [`Node::get`]. Nodes share the
/// same index mapping as their tree, unless a node was [`isolated`]. Once a
/// node has been isolated it uses a new index mapping. The isolated node itself
/// will have index `0`. Its descendants will have indices starting at `1`
/// counting upwards. As a result ancestors of the isolated nodes can no longer
/// be accessed, either by iteration or indices. It is best to consider an
/// isolated node as its own new tree with entirely different indices for the
/// contained nodes.
///
/// Indices expose information about the relationships between nodes in a tree.
/// Any node `child` with an index that is greater than the index of a node
/// `parent` but does not exceed `parent.index() + parent.len()` is a
/// [`Descendant`] of `parent`. This range of indices including the index of
/// `parent` is called the [`Scope`] of `parent`.
///
/// # Examples
///
/// First we show that you can access any node by its index. See [`small_tree`]
/// for more information about the tree we are using.
///
/// We then see that iterating over the indices in the scope of a node is
/// similar to iterating over its descendants. The difference is that the scope
/// includes the index of the node itself.
///
/// ```rust
/// let tree = read_tree::demo::small_tree();
///
/// assert_eq!(tree.get(0).unwrap().data(), &1);
/// assert_eq!(tree.get(1).unwrap().data(), &11);
/// assert_eq!(tree.get(2).unwrap().data(), &12);
/// assert_eq!(tree.get(3).unwrap().data(), &121);
/// // ...
///
/// // All nodes with index within the scope are the original node and its descendants.
/// let scope = tree.get(4).unwrap().scope();
/// assert_eq!(scope, 4..=6);
/// assert!(scope
///     .map(|i| tree.get(i).unwrap().data().to_string())
///     .all(|s| s.starts_with("122")));
/// ```
///
/// We now show how indexing works on nodes. Nodes use the same indices as their
/// tree; this allows accessing any other node in the tree from any node.
///
/// Once a node is isolated however, it uses its own index map. This new shorter
/// index map only indexes nodes within the subtree of the isolated node. The
/// isolated node automatically receives index `0`. It is then impossible to
/// access ancestors of the isolated node. Even the [`Ancestors`] iterator will
/// fail to leave the bounds of the isolation.
///
/// ```rust
/// let tree = read_tree::demo::small_tree();
///
/// let node = tree.get(5).unwrap();
/// assert_eq!(node.get(0).unwrap().data(), &1);
/// assert_eq!(node.get(7).unwrap().data(), &123);
///
/// let node = node.isolated();
/// assert_eq!(node.get(0).unwrap().data(), node.data());
/// assert!(node.get(1).is_none());
/// ```
///
/// [`Descendant`]: crate::Descendants
/// [`Ancestors`]: crate::Ancestors
/// [`isolated`]: crate::Node::isolated
/// [`Node::get`]: crate::Node::get
/// [`Node`]: crate::Node
/// [`small_tree`]: crate::demo::small_tree
/// [`Tree::get`]: crate::Tree::get
/// [`Tree`]: crate::Tree
#[derive(Debug, Clone, Copy)]
pub struct Index {
    pub index: usize,
}

impl Index {
    pub fn as_usize(self) -> usize {
        self.index
    }
}

impl<'a, T> From<Node<'a, T>> for Index {
    fn from(node: Node<'a, T>) -> Self {
        Index {
            index: node.index(),
        }
    }
}
