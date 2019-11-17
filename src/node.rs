use crate::{Ancestors, Branch, Children, Descendants, Tree, ValidationError, Vertex};
use std::convert::{TryFrom, TryInto};

/// A node on a [`Tree`] or [`PolyTree`].
///
/// A node is a borrow of a tree and an [`Index`]. You can navigate to related
/// nodes using iterators.
///
/// *It is planned to add a query system that allows querying [`Descendants`]
/// using chains of conditions. Currently only some basic iterators are
/// available.*
///
/// [`Index`]: crate::vocab::Index
/// [`PolyTree`]: crate::PolyTree
#[derive(Debug)]
pub struct Node<'a, T> {
    pub(crate) index: usize,
    pub(crate) verts: &'a [Vertex<T>],
}

impl<'a, T> Node<'a, T> {
    /// Turns a slice of [`Vertices`][Vertex] into a [`Node`], after performing
    /// some validations.
    ///
    /// To avoid validations; which have a significant cost for large slices;
    /// use the unsafe alternative [`from_slice_unchecked`].
    ///
    /// # Errors
    ///
    /// If the slice does not contain a valid tree structure one of the
    /// following errors is returned.
    ///
    /// 1. `Empty`
    ///
    ///    The slice must not be empty.
    /// 2. `MutlipleRoots`
    ///
    ///    The [`Scope`] of the first vertex must contain the entire slice.
    /// 3. `IllegalStructure`
    ///
    ///    The scope of every vertex in the slice must be contained in the
    ///    scope of its parent.
    ///
    /// [`from_slice_unchecked`]: Node::from_slice_unchecked
    /// [`Scope`]: crate::vocab::Scope
    pub fn from_slice(slice: &'a [Vertex<T>]) -> Result<Self, ValidationError> {
        slice.try_into()
    }

    /// Turns a slice of [`Vertices`][Vertex] into a [`Node`].
    ///
    /// This is the unsafe alternative to [`from_slice`]. The cost of this
    /// method is free.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that all expected qualities of the vertex
    /// slice are fulfilled.
    ///
    /// 1. The slice must not be empty.
    /// 2. The [`Scope`] of the first vertex must contain the entire slice.
    /// 3. The scope of every vertex in the slice must be contained in the
    ///    scope of its parent.
    ///
    /// [`from_slice`]: Node::from_slice
    /// [`Scope`]: crate::vocab::Scope
    pub unsafe fn from_slice_unchecked(slice: &'a [Vertex<T>]) -> Self {
        Node {
            index: 0,
            verts: slice,
        }
    }

    /// Returns the [`Index`] of the node.
    ///
    /// [`Index`]: crate::vocab::Index
    pub fn index(self) -> usize {
        self.index
    }

    /// Returns the [`Scope`] of the node.
    ///
    /// [`Scope`]: crate::vocab::Scope
    pub fn scope(self) -> std::ops::RangeInclusive<usize> {
        self.index()..=self.index() + self.len()
    }

    /// Returns the number of [`Descendants`] of the node.
    ///
    /// A leaf node returns length `0`.
    pub fn len(self) -> usize {
        self.verts[self.index].len
    }

    /// Returns `true` if the node has no [`Children`].
    pub fn is_empty(self) -> bool {
        self.verts[self.index].len == 0
    }

    /// Returns a reference to the payload of the node.
    pub fn data(self) -> &'a T {
        &self.verts[self.index].data
    }

    /// Returns the internal slice of [`Vertices`][Vertex].
    pub fn as_slice(self) -> &'a [Vertex<T>] {
        &self.verts[..]
    }

    /// Returns the node with the specified [`Index`].
    ///
    /// [`Index`]: crate::vocab::Index
    /// [`isolated`]: Node::isolated
    pub fn get(self, index: usize) -> Option<Node<'a, T>> {
        if index >= self.verts.len() {
            return None;
        }

        Some(Node {
            index,
            verts: self.verts,
        })
    }

    /// Returns the parent of the node or `None` if it does not have one.
    pub fn parent(self) -> Option<Node<'a, T>> {
        self.ancestors().next()
    }

    /// Returns the [`Children`] of the node.
    pub fn children(self) -> Children<'a, T> {
        self.into()
    }

    /// Returns the [`Descendants`] of the node.
    pub fn descendants(self) -> Descendants<'a, T> {
        self.into()
    }

    /// Returns the [`Ancestors`] of the node.
    pub fn ancestors(self) -> Ancestors<'a, T> {
        self.into()
    }

    /// Returns the node isolated from the rest of the tree.
    ///
    /// This changes every nodes [`Index`]. The isolated node will always have
    /// index `0`, and it will be impossible to access its [`Ancestors`].
    ///
    /// [`Index`]: crate::vocab::Index
    pub fn isolated(self) -> Node<'a, T> {
        Node {
            index: 0,
            verts: &self.verts[self.index..=self.index + self.verts[self.index].len],
        }
    }
}

impl<'a, T, ASM> From<&'a Tree<T, ASM>> for Node<'a, T> {
    fn from(tree: &'a Tree<T, ASM>) -> Self {
        tree.get(0).unwrap()
    }
}

impl<'a, T> TryFrom<Branch<'a, T>> for Node<'a, T> {
    type Error = ValidationError;

    fn try_from(branch: Branch<'a, T>) -> Result<Self, Self::Error> {
        if branch.get(0).unwrap().len() + 1 != branch.len() {
            return Err(ValidationError::MultipleRoots);
        }

        Ok(branch.get(0).unwrap())
    }
}

impl<'a, T> TryFrom<&'a [Vertex<T>]> for Node<'a, T> {
    type Error = ValidationError;

    fn try_from(slice: &'a [Vertex<T>]) -> Result<Self, Self::Error> {
        Branch::try_from(slice)?.try_into()
    }
}

impl<'a, T> Copy for Node<'a, T> {}

impl<'a, T> Clone for Node<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}
