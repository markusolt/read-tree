//! This crate provides a library for creating and then reading trees. The trees
//! cannot be modified after creation.
//!
//! # Usage
//!
//! This crate is available [on crates.io](https://crates.io/crates/read-tree)
//! and can be used by adding `read-tree` to your dependencies in your projects
//! `Cargo.toml`.
//!
//! ```toml
//! [dependencies]
//! read-tree = "0.1"
//! ```
//!
//! # Example
//!
//! Trees are created using the builder struct [Sapling][Sapling]. Nodes can be
//! attached to a sapling by using `push(_)`. When a node is added to a sapling
//! it is also selected as the parent for later nodes. To finish a node and
//! select its parent use `pop()`. When adding a node with no children
//! `push_leaf(_)` can be used; it behaves the same as `push(_); pop();`.
//!
//! When the sapling is complete you can use `build()` to turn the sapling into
//! a [Tree][Tree]. The resulting tree can no longer be modified. Navigating
//! trees is done by using slices of trees called [Node][Node]s. To get started
//! use `root()` on a tree to get its root node which covers the entire tree.
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

pub use tree::{Children, Descendants, Error, Node, PolyTree, Sapling, Tree};
