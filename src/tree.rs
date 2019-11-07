//! Types for storing and exploring trees.

use crate::iter::{Ancestors, Children, Descendants};

/// An error returned when validating a vertex slice.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum ValidationError {
    /// The vertex slice is empty.
    ///
    /// Nodes must always have exactly one root. The buffer therefor needs to
    /// have at least one entry.
    Empty,

    /// The vertex slice contains more than one root node.
    ///
    /// Nodes can only have exactly one root node.
    MultipleRoots,

    /// Some of the lengths of the vertices do not match up. Ensure a vertex
    /// does not have more descendants than its ancestors.
    IllegalStructure,
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "Empty vertex slice"),
            Self::MultipleRoots => write!(f, "Multiple roots in vertex slice"),
            Self::IllegalStructure => write!(f, "Vertex with invalid length"),
        }
    }
}

impl std::error::Error for ValidationError {}

/// An internal type that stores the payload and relationships of a node in a
/// [`Tree`]`<T>` or [`PolyTree`]`<T>`.
///
/// Every node on the tree is represented by a [`Vertex`]`<T>`. The `len` field
/// stores the number of descendants the node has; this is the number of nodes
/// in the subtree below the node. A leaf node has length `0`.
///
/// Every [`Tree`]`<T>` contains a [`Vec`]`<`[`Vertex`]`<T>>` representing the
/// trees nodes in a depth first order; meaning every vertex is followed by its
/// first child. This makes it very easy to take a slice of the vertex buffer
/// that represents a subtree. We expose such a slice to the user as a
/// [`Node`]`<T>`.
///
/// The type implements [`Clone`] and [`Copy`] as long as the payload `T`
/// implements the same. Supporting [`Copy`] is important to ensure
/// [`Vec::extend_from_slice`] executes as fast as possible. This method is used
/// by [`Sapling::push_tree`] to copy the nodes of a tree into another sapling.
///
/// [`Sapling::push_tree`]: crate::Sapling::push_tree
#[derive(Debug, Clone, Copy)]
pub struct Vertex<T> {
    pub data: T,
    pub len: usize,
}

impl<T> Vertex<T> {
    /// Returns a new vertex with payload `data` intending to own `len` many
    /// descendants.
    pub fn new(data: T, len: usize) -> Self {
        Vertex { data, len }
    }
}

/// A read-only tree data structure.
///
/// Trees are created from [`Sapling`]`<T>`s. Most interactions with trees
/// happen on slices of them called [`Node`]s. Get a node representing the
/// entire tree using [`as_node`].
///
/// [`as_node`]: Tree::as_node
///
/// [`Sapling`]: crate::Sapling
#[derive(Debug, Clone)]
pub struct Tree<T> {
    /// Unused buffer.
    ///
    /// The buffer was used by the sapling that was used to construct the tree.
    /// It is kept in case the tree is turned back into a sapling.
    pub(crate) open: Vec<usize>,
    pub(crate) verts: Vec<Vertex<T>>,
}

#[allow(clippy::len_without_is_empty)]
impl<T> Tree<T> {
    /// Returns the unique root node of the tree representing the entire tree.
    ///
    /// You can think of this as taking the complete slice of the tree similar
    /// to `&vec[..]` for a [`Vec`]`<T>`.
    pub fn as_node(&self) -> Node<T> {
        Node {
            index: 0,
            verts: &self.verts[..],
        }
    }

    /// Returns the node with the specified `index`.
    pub fn get(&self, index: usize) -> Option<Node<T>> {
        if index >= self.verts.len() {
            return None;
        }

        Some(Node {
            index,
            verts: &self.verts[..],
        })
    }

    /// Returns the number of nodes in the tree.
    ///
    /// Because trees are required to have exactly one root node, the length
    /// will always be at least `1`.
    pub fn len(&self) -> usize {
        self.verts.len()
    }

    pub fn iter(&self) -> Descendants<T> {
        self.into()
    }
}

/// A read-only poly-tree data structure.
///
/// Similar to [`Tree`]`<T>` but allows multiple root nodes.
#[derive(Debug, Clone)]
pub struct PolyTree<T> {
    pub(crate) open: Vec<usize>,
    pub(crate) verts: Vec<Vertex<T>>,
}

#[allow(clippy::len_without_is_empty)]
impl<T> PolyTree<T> {
    pub fn roots(&self) -> Children<T> {
        self.into()
    }

    /// Returns the node with the specified `index`.
    pub fn get(&self, index: usize) -> Option<Node<T>> {
        if index >= self.verts.len() {
            return None;
        }

        Some(Node {
            index,
            verts: &self.verts[..],
        })
    }

    /// Returns the number of nodes in the poly-tree.
    ///
    /// Because poly-trees are required to not be empty, the length will always
    /// be at least `1`.
    pub fn len(&self) -> usize {
        self.verts.len()
    }
}

#[derive(Debug)]
pub struct Branch<'a, T> {
    verts: &'a [Vertex<T>],
}

impl<'a, T> Branch<'a, T> {
    pub fn from_slice(verts: &'a [Vertex<T>]) -> Result<Self, ValidationError> {
        if verts.is_empty() {
            return Err(ValidationError::Empty);
        }

        let mut open = Vec::new();
        for (i, val) in verts.iter().enumerate() {
            while open.last() == Some(&i) {
                open.pop().ok_or(ValidationError::IllegalStructure)?;
            }

            let scope = i + val.len + 1;
            if open.last().map(|head| *head < scope) == Some(true) {
                return Err(ValidationError::IllegalStructure);
            }
            open.push(scope);
        }
        std::mem::drop(open);

        Ok(Branch { verts })
    }

    pub unsafe fn from_slice_unchecked(verts: &'a [Vertex<T>]) -> Self {
        Branch { verts }
    }

    pub fn len(self) -> usize {
        self.verts.len()
    }

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

impl<'a, T> From<&'a Tree<T>> for Branch<'a, T> {
    fn from(tree: &'a Tree<T>) -> Self {
        Branch { verts: &tree.verts }
    }
}

impl<'a, T> From<&'a PolyTree<T>> for Branch<'a, T> {
    fn from(tree: &'a PolyTree<T>) -> Self {
        Branch { verts: &tree.verts }
    }
}

impl<'a, T> From<Node<'a, T>> for Branch<'a, T> {
    fn from(node: Node<'a, T>) -> Self {
        Branch { verts: node.verts }
    }
}

impl<'a, T> Copy for Branch<'a, T> {}

impl<'a, T> Clone for Branch<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}

/// A slice of a [`Tree`]`<T>` or [`PolyTree`]`<T>`.
///
/// A node is essentially the same as a tree, except it does not own its data.
///
/// Navigating the subtree of a node is done using iterators.
///
/// *It is planned to add a query type that allows querying nodes from subtrees
/// using chains of conditions. Currently only some basic iterators are
/// available.*
#[derive(Debug)]
pub struct Node<'a, T> {
    index: usize,
    verts: &'a [Vertex<T>],
}

impl<'a, T> Node<'a, T> {
    /// Turns a slice of vertices into a [`Node`]`<T>`, after performing some
    /// validations.
    ///
    /// Returns an error in case of a failed validation. For the possible errors
    /// see [`ValidationError`]. For a more detailed description of the
    /// validation process see the safety section for [`from_unchecked`].
    ///
    /// To avoid running the validations; which have a significant cost for
    /// large trees; use the unsafe alternative [`from_unchecked`].
    ///
    /// [`from_unchecked`]: Node::from_unchecked
    pub fn from(verts: &[Vertex<T>]) -> Result<Node<T>, ValidationError> {
        if verts.is_empty() {
            return Err(ValidationError::Empty);
        }
        if verts.len() != verts[0].len + 1 {
            return Err(ValidationError::MultipleRoots);
        }

        Ok(Node {
            index: 0,
            verts: Branch::from_slice(verts)?.verts,
        })
    }

    /// Returns a slice of vertices as a [`Node`]`<T>`.
    ///
    /// This is the unsafe alternative to [`from`] that skips all validations.
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
    /// [`from`]: Node::from
    pub unsafe fn from_unchecked(verts: &[Vertex<T>]) -> Node<T> {
        Node { index: 0, verts }
    }

    /// Returns a reference to the payload of the node.
    pub fn data(self) -> &'a T {
        &self.verts[self.index].data
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
    pub fn scope(self) -> (usize, usize) {
        (self.index(), self.index() + self.len())
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

    /// Returns the internal slice of [`Vertices`][Vertex].
    pub fn verts(self) -> &'a [Vertex<T>] {
        &self.verts[self.index()..=self.index() + self.len()]
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
        Children::from(self)
    }

    /// Returns the [`Descendants`] of the node.
    pub fn descendants(self) -> Descendants<'a, T> {
        Descendants::from(self)
    }

    /// Returns the [`Ancestors`] of the node.
    pub fn ancestors(self) -> Ancestors<'a, T> {
        Ancestors::from(self)
    }

    /// Returns the nodes internal vertex slice.
    pub fn as_slice(self) -> &'a [Vertex<T>] {
        self.verts
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

    /// Clones the contents of the node into a new [`Tree`]`<T>`.
    ///
    /// Similar to [`push_node`] this operation is cheaper if `T` implements
    /// [`Copy`]. It is internally based on [`Vec::extend_from_slice`].
    ///
    /// [`push_node`]: crate::Sapling::push_node
    pub fn into_tree(self) -> Tree<T>
    where
        T: Clone,
    {
        let mut verts = Vec::new();
        verts.extend_from_slice(self.verts);

        Tree {
            open: Vec::new(),
            verts,
        }
    }
}

impl<'a, T> Copy for Node<'a, T> {}

impl<'a, T> Clone for Node<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}
