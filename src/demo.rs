//! Functions relevant for examples.

use crate::{Sapling, Tree};

/// Returns a small [`Tree`].
///
/// This function is used throughout the examples within this crate. It always
/// returns the same tree. The tree has `8` nodes as they are drawn below.
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_small_tree() {
        let tree = small_tree();
        let mut iter = tree.iter();

        let node = iter.next().unwrap();
        assert_eq!(node.index(), 0);
        assert_eq!(node.len(), 7);
        assert_eq!(node.scope(), 0..=7);
        assert_eq!(node.data(), &1);

        let node = iter.next().unwrap();
        assert_eq!(node.index(), 1);
        assert_eq!(node.len(), 0);
        assert_eq!(node.scope(), 1..=1);
        assert_eq!(node.data(), &11);

        let node = iter.next().unwrap();
        assert_eq!(node.index(), 2);
        assert_eq!(node.len(), 5);
        assert_eq!(node.scope(), 2..=7);
        assert_eq!(node.data(), &12);

        let node = iter.next().unwrap();
        assert_eq!(node.index(), 3);
        assert_eq!(node.len(), 0);
        assert_eq!(node.scope(), 3..=3);
        assert_eq!(node.data(), &121);

        let node = iter.next().unwrap();
        assert_eq!(node.index(), 4);
        assert_eq!(node.len(), 2);
        assert_eq!(node.scope(), 4..=6);
        assert_eq!(node.data(), &122);

        let node = iter.next().unwrap();
        assert_eq!(node.index(), 5);
        assert_eq!(node.len(), 0);
        assert_eq!(node.scope(), 5..=5);
        assert_eq!(node.data(), &1221);

        let node = iter.next().unwrap();
        assert_eq!(node.index(), 6);
        assert_eq!(node.len(), 0);
        assert_eq!(node.scope(), 6..=6);
        assert_eq!(node.data(), &1222);

        let node = iter.next().unwrap();
        assert_eq!(node.index(), 7);
        assert_eq!(node.len(), 0);
        assert_eq!(node.scope(), 7..=7);
        assert_eq!(node.data(), &123);

        assert!(iter.next().is_none());
    }
}
