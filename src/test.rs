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

mod test_sapling {
    use super::*;

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

mod test_tree {
    use super::*;

    #[test]
    fn test_from() {
        let tree = small();
        let tree_2 = Tree::from(tree.root());
        for (n1, n2) in tree.root().iter().zip(tree_2.root().iter()) {
            assert_eq!(n1.data(), n2.data());
        }
    }
}

mod test_iter {
    use super::*;

    #[test]
    fn test_iter_children() {
        let tree = small();
        let mut iter = tree.root().children();

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 1);
        assert_eq!(node.data(), &11);

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 1);
        assert_eq!(node.data(), &12);

        assert!(iter.next().is_none());
    }

    #[test]
    fn test_iter_descendants() {
        let tree = small();
        let mut iter = tree.root().iter();

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 0);
        assert_eq!(node.data(), &1);

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 1);
        assert_eq!(node.data(), &11);

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 1);
        assert_eq!(node.data(), &12);

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 2);
        assert_eq!(node.data(), &121);

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 3);
        assert_eq!(node.data(), &1211);

        let node = iter.next().unwrap();
        assert_eq!(node.depth(), 2);
        assert_eq!(node.data(), &122);

        assert!(iter.next().is_none());
    }
}
