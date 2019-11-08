//! This crate provides a library for creating and then querying trees. The
//! trees are not intended to be modified after their initial creation.
//!
//! Internally trees are represented by a [`Vec`]`<`[`Vertex`]`<T>>` where each
//! vertex carries the payload of that node in the tree and the number of its
//! descendants. In addition the vertices are sorted depth first; meaning every
//! vertex is followed by the vertex of its first child. Using the length of a
//! vertex we can easily skip a nodes entire subtree and can instantly access
//! its sibling.
//!
//! Slicing a tree into a node is as simple as slicing the trees vertices buffer
//! into a `&[`[`Vertex`]`<T>]`. We wrap this slice in a [`Node`]`<T>`.
//!
//! # Examples
//!
//! Trees are created using [`Sapling`]s. Nodes can be attached to a sapling by
//! using [`push`]. When a node is added to a sapling it is also selected as the
//! parent for nodes that are added later. To finish a node and reselect its
//! parent call [`pop`]. When adding a node with no children use [`push_leaf`].
//! There are more methods to push other saplings, trees or even nodes. See
//! [`Sapling`] for more information.
//!
//! When the sapling is complete, you can [`build`] it into a [`Tree`]`<T>`. The
//! resulting tree can no longer be modified. Navigating trees is done by using
//! slices of trees called [`Node`]`<T>`. To get started use [`as_node`] on a
//! tree to get its root node which represents the entire tree.
//!
//! Nodes support various iterators to navigate their contents.
//!
//! ```rust
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     use read_tree::Sapling;
//!
//!     let mut sap = Sapling::new();
//!     sap.push(1);
//!     sap.pop();
//!
//!     let tree = sap.build()?;
//!     let root = tree.as_node();
//!
//!     assert_eq!(root.data(), &1);
//!     Ok(())
//! }
//! ```
//!
//! [`as_node`]: Tree::as_node
//! [`build`]: Sapling::build
//! [`pop`]: Sapling::pop
//! [`push_leaf`]: Sapling::push_leaf
//! [`push`]: Sapling::push

mod iter;
mod sapling;
mod tree;

pub mod demo;
pub mod error;
pub mod vocab;

pub use iter::{Ancestors, Children, Descendants};
pub use sapling::{BuildError, Sapling};
pub use tree::{Branch, Node, PolyTree, Tree, ValidationError, Vertex};

#[cfg(test)]
mod test;
