//! This crate provides a library for creating and then querying trees. The
//! trees are not intended to be modified after their initial creation.
//!
//! Internally trees are represented by a [Vec] of vertices where each vertex
//! carries the payload of that node in the tree and the number of nodes in the
//! subtree of the node, called the length of the vertex. In addition the
//! vertices are sorted depth first; meaning every vertex is followed by the
//! vertex of its first child. Using the length of a vertex we can easily skip a
//! nodes entire subtree and can instantly access its sibling.
//!
//! Slicing a tree into a node is as simple as slicing the trees [Vec] of
//! vertices into a `&[Vertex<T>]` slice.
//!
//! # Example
//!
//! Trees are created using the builder struct [Sapling][Sapling]. Nodes can be
//! attached to a sapling by using `.push(_)`. When a node is added to a sapling
//! it is also selected as the parent for later nodes. To finish a node and
//! reselect its parent use `.pop()`. When adding a node with no children use
//! `.push_leaf(_)`; it behaves the same as `.push(_); .pop();`.
//!
//! When the sapling is complete, you can use `.build()` to turn the sapling
//! into a [Tree][Tree]. The resulting tree can no longer be modified.
//! Navigating trees is done by using slices of trees called [Node][Node]s. To
//! get started use `.root()` on a tree to get its root node which contains the
//! entire tree.
//!
//! Nodes support various iterators to navigate their contents.
//!
//! ```rust
//! use read_tree::Sapling;
//!
//! let mut sap = Sapling::new();
//! sap.push(1);
//! sap.pop();
//!
//! let tree = sap.build().unwrap();
//! let root = tree.root();
//!
//! assert_eq!(root.data(), &1);
//! ```

mod tree;

#[cfg(test)]
mod test;

pub use tree::{
    Ancestors, BuildError, Children, Descendants, Node, PolyTree, Sapling, Tree, ValidationError,
    Vertex,
};
