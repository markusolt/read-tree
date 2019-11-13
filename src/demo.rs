//! Functions relevant for examples.

use crate::{Sapling, Tree};

/// Returns a small [`Tree`].
///
/// This function is used throughout the examples within this crate. It always
/// returns the same tree. The tree has `8` [`Nodes`] as they are drawn below.
///
/// ```text
/// (0) - 1
/// (1)     - 11
/// (2)     - 12
/// (3)         - 121
/// (4)         - 122
/// (5)             - 1221
/// (6)             - 1222
/// (7)         - 123
/// ```
///
/// [`Nodes`]: crate::Node
/// [`Tree`]: crate::Tree
pub fn small_tree() -> Tree<usize> {
    let mut sap = Sapling::new();

    sap.push(1);
    sap.push_leaf(11);
    sap.push(12);
    sap.push_leaf(121);
    sap.push(122);
    sap.push_leaf(1221);
    sap.push_leaf(1222);
    sap.pop();
    sap.push_leaf(123);
    sap.pop();
    sap.pop();

    sap.build().unwrap()
}
