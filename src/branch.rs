use crate::{Node, PolyTree, Tree, ValidationError, Vertex};
use std::convert::{TryFrom, TryInto};

/// A group of [`Nodes`].
///
/// A branch is a slice of a [`Tree`], but unlike [`Node`] it can contain
/// multiple nodes. While a node represents a [`Tree`], a branch represents a
/// [`PolyTree`].
///
/// Most tree related types can safely be turned into branches. It is used
/// internally by node iterators such as [`Children`].
///
/// [`Children`]: crate::Children
/// [`Nodes`]: crate::Node
/// [`PolyTree`]: crate::PolyTree
/// [`Tree`]: crate::Tree
#[derive(Debug)]
pub struct Branch<'a, T> {
    verts: &'a [Vertex<T>],
}

impl<'a, T> Branch<'a, T> {
    /// Wraps a `&[`[`Vertex`]`<T>]` slice into a branch.
    ///
    /// # Errors
    ///
    /// The method will return an error if the slice does not represent a valid
    /// branch. Unlike [`Node::from_slice`], branches do not require a single
    /// root node spanning the entire slice. The following [`ValidationErrors`]
    /// can occur.
    ///
    /// 1. `Empty`
    ///
    ///    Branches are not allowed to be empty.
    /// 2. `IllegalStructure`
    ///
    ///    The [`scope`] of every vertex in the slice must be contained in its
    ///    parent scope.
    ///
    /// [`Node::from_slice`]: crate::Node::from_slice
    /// [`scope`]: crate::vocab::Scope
    /// [`ValidationErrors`]: crate::ValidationError
    /// [`Vertex`]: crate::Vertex
    pub fn from_slice(slice: &'a [Vertex<T>]) -> Result<Self, ValidationError> {
        slice.try_into()
    }

    /// The validations of [`from_slice`] can have a significant cost for large
    /// slices. This method wraps a slice into a branch without performing any
    /// validations.
    ///
    /// # Safety
    ///
    /// It is up to the caller to ensure the following qualities of the slice.
    ///
    /// 1. The slice must not be empty.
    /// 2. The [`scope`] of every [`Vertex`] in the slice must be contained
    ///    within the scope of its parent vertex.
    ///
    /// See [`Sapling`] for an abstraction that safely calls this method to
    /// avoid unnecessary validations.
    ///
    /// [`from_slice`]: crate::Branch::from_slice
    /// [`Node::from_slice_unchecked`]: crate::Node::from_slice_unchecked
    /// [`Sapling`]: crate::Sapling
    /// [`scope`]: crate::vocab::Scope
    pub unsafe fn from_slice_unchecked(slice: &'a [Vertex<T>]) -> Self {
        Branch { verts: slice }
    }

    /// Returns the inner slice of [`Vertices`] representing the branch.
    ///
    /// [`Vertices`]: crate::Vertex
    pub fn as_slice(self) -> &'a [Vertex<T>] {
        &self.verts[..]
    }

    /// Returns the number of [`Nodes`] in the branch. This is equivalent to
    /// `branch.as_slice().len()`.
    ///
    /// [`Nodes`]: crate::Node
    pub fn len(self) -> usize {
        self.verts.len()
    }

    /// Returns the [`Node`] with the specified [`Index`].
    ///
    /// The index is relative to the branch, meaning the indices of the nodes in
    /// the branch are within `0..branch.len()`.
    ///
    /// [`Index`]: crate::vocab::Index
    /// [`Node`]: crate::Node
    pub fn get(self, index: usize) -> Option<Node<'a, T>> {
        if index >= self.verts.len() {
            return None;
        }

        Some(Node {
            index,
            verts: self.verts,
        })
    }
}

impl<'a, T, ASM> From<&'a Tree<T, ASM>> for Branch<'a, T> {
    fn from(tree: &'a Tree<T, ASM>) -> Self {
        Branch {
            verts: tree.sap.as_slice(),
        }
    }
}

impl<'a, T, ASM> From<&'a PolyTree<T, ASM>> for Branch<'a, T> {
    fn from(tree: &'a PolyTree<T, ASM>) -> Self {
        Branch {
            verts: tree.sap.as_slice(),
        }
    }
}

impl<'a, T> From<Node<'a, T>> for Branch<'a, T> {
    fn from(node: Node<'a, T>) -> Self {
        Branch {
            verts: node.as_slice(),
        }
    }
}

impl<'a, T> TryFrom<&'a [Vertex<T>]> for Branch<'a, T> {
    type Error = ValidationError;

    fn try_from(slice: &'a [Vertex<T>]) -> Result<Self, Self::Error> {
        if slice.is_empty() {
            return Err(ValidationError::Empty);
        }

        let mut open = Vec::new();
        for (i, val) in slice.iter().enumerate() {
            while open.last() == Some(&i) {
                open.pop().ok_or(ValidationError::IllegalStructure)?;
            }

            let scope = i + val.len + 1;
            if open.last().map(|head| *head < scope) == Some(true) {
                return Err(ValidationError::IllegalStructure);
            }
            open.push(scope);
        }

        Ok(Branch { verts: slice })
    }
}

impl<'a, T> Copy for Branch<'a, T> {}

impl<'a, T> Clone for Branch<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}
