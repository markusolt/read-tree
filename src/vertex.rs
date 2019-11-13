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
