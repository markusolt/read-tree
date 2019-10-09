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
//! let mut sap = Sapling::new();
//! sap.push(1);
//! sap.pop();
//!
//! let tree = sap.build().unwrap();
//! let root = tree.root();
//!
//! assert_eq!(root.data(), &1);
//! ```

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
    /// When creating nodes on a sapling it is possible to finish the root node
    /// and add a second one. Trees however must have a unique root.
    MultipleRoots,
}

#[derive(Debug)]
struct Vertex<T> {
    len: usize,
    data: T,
}

/// A build struct to construct a new [Tree][Tree].
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

    /// Adds a new node with the payload `data` to the sapling.
    ///
    /// Selects the new node.
    pub fn push(&mut self, data: T) {
        self.path.push(self.verts.len());
        self.verts.push(Vertex { len: 0, data });
    }

    /// Adds a new node with the payload `data` to the sapling.
    ///
    /// Does not change selection.
    pub fn push_leaf(&mut self, data: T) {
        self.verts.push(Vertex { len: 0, data });
    }

    /// Attaches another tree to the selected node.
    ///
    /// Does not change selection. Returns an empty sapling that is reusing the
    /// internal buffer of the consumed tree `other`.
    pub fn push_tree(&mut self, other: Tree<T>) -> Sapling<T> {
        let mut verts = other.verts;
        self.verts.append(&mut verts);
        Sapling {
            path: Vec::new(),
            verts,
        }
    }

    /// Closes the selected node.
    ///
    /// Selects the parent of the closed node. Returns `None` if there was no
    /// node to close.
    pub fn pop(&mut self) -> Option<()> {
        let i = self.path.pop()?;
        self.verts[i].len = self.verts.len() - i - 1;
        Some(())
    }

    /// Removes all nodes from the sapling, making it empty.
    pub fn clear(&mut self) {
        self.path.clear();
        self.verts.clear();
    }

    /// Returns `true` if the sapling has no nodes.
    pub fn is_empty(&self) -> bool {
        self.verts.is_empty()
    }

    /// Return `true` if the sapling is ready to be built.
    ///
    /// Verifies that the sapling is not empty and has no open nodes. It does
    /// not verify the number of root nodes of the sapling.
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
    /// Returns the unique root node of the tree representing the entire tree.
    ///
    /// You can think of this as taking the complete slice of the tree similar
    /// to `&vec[..]` for a [Vec][std::vec::Vec] `vec`.
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

    /// Returns a depth first iterator of nodes. It iterates all nodes in the
    /// subtree of the node, including the node itself. See
    /// [Descendants][Descendants] for more information.
    pub fn iter(&self) -> Descendants<'a, T> {
        Descendants { verts: self.verts }
    }

    /// Returns an iterator over the child nodes of the node. See
    /// [Children][Children] for more information.
    pub fn children(&self) -> Children<'a, T> {
        Children {
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
    verts: &'a [Vertex<T>],
}

impl<'a, T> Iterator for Descendants<'a, T> {
    type Item = Node<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let verts = &self.verts[0..self.verts.get(0)?.len + 1];
        self.verts = &self.verts[1..];
        Some(Node { verts })
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
    verts: &'a [Vertex<T>],
}

impl<'a, T> Iterator for Children<'a, T> {
    type Item = Node<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let (verts, remainder) = &self.verts.split_at(self.verts.get(0)?.len + 1);
        self.verts = remainder;
        Some(Node { verts })
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
}
