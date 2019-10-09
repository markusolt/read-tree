# read-tree

A rust library for creating and then navigating read-only trees.

# Usage

Add the following to your `cargo.toml` file.

```toml
[dependencies]
read-tree = "0.1"
```

Trees are created using the builder struct `Sapling`. Nodes can be attached to
a sapling by using `push(_)`. When a node is added to a sapling it is also
selected as the parent for later nodes. To finish a node and select its parent
use `pop()`. When adding a node with no children `push_leaf(_)` can be used;
it behaves the same as `push(_); pop();`.

All changes to a sapling return a `Result`. This is done because the sapling
ensures certain qualities of your tree. For instance it ensures there is
exactly one root.

When the sapling is complete you can use `build()` to turn the sapling into
a `Tree`. The resulting tree can no longer be modified. Navigating trees is
done by using slices of trees called `Node`s. To get started use `root()` on a
tree to get its root node.

Nodes support various iterators to navigate their contents.

```rust
use read-tree::Sapling;

let sap = Sapling::new();
sap.push(1).unwrap();

let tree = sap.build().unwrap();
let root = tree.root();

assert_eq!(root.data, 1);
```
