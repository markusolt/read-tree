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
//! All changes to a sapling return a `Result`. This is done because the sapling
//! ensures certain qualities of your tree. For instance it ensures there is
//! exactly one root.
//!
//! When the sapling is complete you can use `build()` to turn the sapling into
//! a [Tree][Tree]. The resulting tree can no longer be modified. Navigating
//! trees is done by using slices of trees called [Node][Node]s. To get started
//! use `root()` on a tree to get its root node.
//!
//! Nodes support various iterators to navigate their contents.
//!
//! ```rust
//! use read_tree::Sapling;
//!
//! let sap = Sapling::new();
//! sap.push(1).unwrap();
//!
//! let tree = sap.build().unwrap();
//! let root = tree.root();
//!
//! assert_eq!(root.data, 1);
//! ```

#![deny(missing_docs)]

/// An error enum returned by [Sapling][Sapling] for various mutating
/// operations.
#[derive(Debug)]
pub enum Error {
    /// Failed to add a new node to a sapling. Occurs when the root node has
    /// already been closed and creating a new node would create a second root
    /// in the sapling.
    Push,

    /// Failed to close the current node. Occurs when there is no selected node.
    Pop,

    /// Sapling is incomplete. Occurs when trying to build an incomplete
    /// sapling.
    NotComplete,
}

#[derive(Debug)]
struct Vertex<T> {
    len: usize,
    data: T,
}

/// A build struct to construct new [Tree][Tree]s.
#[derive(Debug)]
pub struct Sapling<T> {
    path: Vec<usize>,
    verts: Vec<Vertex<T>>,
}

impl<T> Sapling<T> {
    /// Creates a new empty sapling.
    ///
    /// Saplings are used to create [Tree][Tree]s. Add nodes using `push(_)` and
    /// `pop()`. Then `build()` the sapling into a tree.
    pub fn new() -> Self {
        Sapling {
            path: Vec::new(),
            verts: Vec::new(),
        }
    }

    /// Adds a new node carrying `data` to the sapling.
    ///
    /// Selects the new node. Fails when no node is selected.
    pub fn push(&mut self, data: T) -> Result<(), Error> {
        if self.complete() {
            return Err(Error::Push);
        }

        self.path.push(self.verts.len());
        self.verts.push(Vertex { len: 0, data });
        Ok(())
    }

    /// Adds a new node carrying `data` to the sapling.
    ///
    /// Does not change selection. The new node will not have any children.
    /// Fails when no node is selected.
    pub fn push_leaf(&mut self, data: T) -> Result<(), Error> {
        if self.complete() {
            return Err(Error::Push);
        }

        self.verts.push(Vertex { len: 0, data });
        Ok(())
    }

    /// Attaches another tree to the selected node.
    ///
    /// Returns an empty sapling that is reusing the internal buffer of the
    /// consumed tree.
    pub fn push_tree(&mut self, other: Tree<T>) -> Result<Sapling<T>, Error> {
        if self.complete() {
            return Err(Error::Push);
        }

        let mut verts = other.verts;
        self.verts.append(&mut verts);
        Ok(Sapling {
            path: Vec::new(),
            verts,
        })
    }

    /// Closes the selected node.
    ///
    /// Selects the parent of the closed node. Fails when no node is selected.
    pub fn pop(&mut self) -> Result<(), Error> {
        let i = self.path.pop().ok_or(Error::Pop)?;
        self.verts[i].len = self.verts.len() - i - 1;
        Ok(())
    }

    /// Removes all nodes from the sapling, making it empty.
    pub fn clear(&mut self) {
        self.path.clear();
        self.verts.clear();
    }

    /// Returns `true` if the sapling has no nodes.
    pub fn empty(&self) -> bool {
        self.verts.is_empty()
    }

    /// Return `true` if the sapling is ready to be built.
    pub fn complete(&self) -> bool {
        self.path.is_empty() && !self.verts.is_empty()
    }

    /// Builds the sapling into a tree.
    ///
    /// Consumes the sapling in the process. Fails when the sapling is
    /// incomplete.
    pub fn build(self) -> Result<Tree<T>, Error> {
        if !self.complete() {
            return Err(Error::NotComplete);
        }

        Ok(Tree { verts: self.verts })
    }
}

/// A read-only tree data structure.
///
/// Trees a created by [Sapling][Sapling]s. Most interactions with trees happen
/// on slices of them called [Node][Node]s.
#[derive(Debug)]
pub struct Tree<T> {
    verts: Vec<Vertex<T>>,
}

impl<T> Tree<T> {
    /// Returns the root node of the tree.
    pub fn root(&self) -> Node<'_, T> {
        Node {
            verts: &self.verts[..],
        }
    }
}

/// A slice of a [Tree][Tree].
///
/// A node is essentially the same as a tree, only that it does not own its
/// data. You can navigate a node using iterators.
#[derive(Debug)]
pub struct Node<'a, T> {
    verts: &'a [Vertex<T>],
}

impl<'a, T> Node<'a, T> {
    /// Returns a reference to the payload of the node.
    pub fn data(&self) -> &T {
        &self.verts[0].data
    }
}
