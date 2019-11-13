use crate::{Ancestors, Branch, Children, Descendants, Tree, ValidationError, Vertex};
use std::convert::{TryFrom, TryInto};

/// A slice of a [`Tree`]`<T>` or [`PolyTree`]`<T>`.
///
/// A node is essentially the same as a tree, except it does not own its data.
///
/// Navigating the subtree of a node is done using iterators.
///
/// *It is planned to add a query type that allows querying nodes from subtrees
/// using chains of conditions. Currently only some basic iterators are
/// available.*
///
/// [`Tree`]: crate::Tree
/// [`PolyTree`]: crate::PolyTree
#[derive(Debug)]
pub struct Node<'a, T> {
    pub(crate) index: usize,
    pub(crate) verts: &'a [Vertex<T>],
}

impl<'a, T> Node<'a, T> {
    /// Turns a slice of vertices into a [`Node`]`<T>`, after performing some
    /// validations.
    ///
    /// Returns an error in case of a failed validation. For the possible errors
    /// see [`ValidationError`]. For a more detailed description of the
    /// validation process see the safety section for [`from_slice_unchecked`].
    ///
    /// To avoid running the validations; which have a significant cost for
    /// large trees; use the unsafe alternative [`from_slice_unchecked`].
    ///
    /// [`from_slice_unchecked`]: Node::from_slice_unchecked
    pub fn from_slice(slice: &'a [Vertex<T>]) -> Result<Self, ValidationError> {
        slice.try_into()
    }

    /// Returns a slice of vertices as a [`Node`]`<T>`.
    ///
    /// This is the unsafe alternative to [`from_slice`] that skips all
    /// validations.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that all expected qualities of the vertex
    /// slice are fulfilled.
    ///
    /// 1. The vertex slice must not be empty.
    /// 2. The first vertex must span the entire slice.
    ///
    ///    This means that the `len` of the first vertex is equal to
    ///    `verts.len() - 1`.
    ///
    /// 3. The scope of all vertices must be contained within the scope of its
    ///    parent vertex
    ///
    ///    Here `scope` refers to the range starting from a nodes index to the
    ///    nodes index plus its `len` inclusive.
    ///
    /// [`from_slice`]: Node::from_slice
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

    /// Returns the number of descending nodes within the subtree of this node.
    /// A leaf node returns length `0`.
    pub fn len(self) -> usize {
        self.verts[self.index].len
    }

    /// Returns `true` if the node has no child nodes.
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

    /// Returns the node with the specified `index`.
    ///
    /// The index must be relative to the trees root, or the most recently
    /// pruned node. See [`isolated`] for more information.
    ///
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
    /// An isolated node will always have index `0`, and it will be impossible
    /// to access its ancestors. It is still possible to explore the subtree
    /// below the node.
    ///
    /// When getting nodes by index you must get them from this or any
    /// descending node. If you use the index in a node that is not affected
    /// by this isolation, it will return some other node. Think of the
    /// isolated node as an entirely new tree with its own indexing.
    pub fn isolated(self) -> Node<'a, T> {
        Node {
            index: 0,
            verts: &self.verts[self.index..=self.index + self.verts[self.index].len],
        }
    }
}

impl<'a, T, ASM> From<&'a Tree<T, ASM>> for Node<'a, T> {
    fn from(tree: &'a Tree<T, ASM>) -> Self {
        Node {
            index: 0,
            verts: tree.as_slice(),
        }
    }
}

impl<'a, T> TryFrom<Branch<'a, T>> for Node<'a, T> {
    type Error = ValidationError;

    fn try_from(branch: Branch<'a, T>) -> Result<Self, Self::Error> {
        if branch.as_slice()[0].len + 1 != branch.len() {
            return Err(ValidationError::MultipleRoots);
        }

        Ok(Node {
            index: 0,
            verts: branch.as_slice(),
        })
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
