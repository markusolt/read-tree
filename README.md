# read-tree

A rust library for creating and then navigating read-only trees.

# Usage

Add the following to your `cargo.toml` file.

```toml
[dependencies]
read-tree = "0.2"
```

# Description

This crate provides a library for creating and then querying trees.
The trees are not intended to be modified after their initial creation.

Internally trees are represented by a `Vec<Vertex<T>>` where each vertex carries the payload of that node in the tree and the number of its descendants.
In addition the vertices are sorted depth first; meaning every vertex is followed by the vertex of its first child.
Using the length of a vertex we can easily skip a nodes entire subtree and can instantly access its sibling.

Slicing a tree into a node is as simple as slicing the trees vertices buffer into a `&[Vertex<T>]`.
We wrap this slice in a `Node<T>`.

# Examples

Trees are created using `Sapling`s.
Nodes can be attached to a sapling by using `push`.
When a node is added to a sapling it is also selected as the parent for nodes that are added later.
To finish a node and reselect its parent call `pop`.
When adding a node with no children use `push_leaf`.
There are more methods to push other saplings, trees or even nodes.
See `Sapling` for more information.

When the sapling is complete, you can `build` it into a `Tree<T>`.
The resulting tree can no longer be modified.
Navigating trees is done by using slices of trees called `Node<T>`.
To get started use `as_node` on a tree to get its root node which represents the entire tree.

Nodes support various iterators to navigate their contents.

```rust
fn main() -> Result<(), Box<dyn std::error::Error>> {
    use read_tree::Sapling;

    let mut sap = Sapling::new();
    sap.push(1);
    sap.pop();

    let tree = sap.build()?;
    let root = tree.as_node();

    assert_eq!(root.data(), &1);
    Ok(())
}
```

# Changelog

# Version `0.2.0`
- Breaking changes
    - Removed `Node::depth`
    - Changed `Node::len` to no longer includes the node itself in the count
    - Changed `Descendants` to no longer include the node itself
    - Renamed `Node::iter` into `Node::descendants`
- Additions
    - Made `Vertex` public
    - Added `PolyTree`
    - Added `Ancestors` iterator
- Improvements
    - Implemented more traits for error enums
    - Implemented more traits and overrides for iterators

# Version `0.1.0`

Initial Release.
