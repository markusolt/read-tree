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

mod test_node {
    use super::*;

    #[test]
    fn test_to_tree() {
        let tree_1 = small();
        let tree_2 = tree_1.root().into_tree();
        for (n1, n2) in tree_1.root().descendants().zip(tree_2.root().descendants()) {
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

        assert_eq!(iter.next().unwrap().data(), &11);
        assert_eq!(iter.next().unwrap().data(), &12);
        assert!(iter.next().is_none());
    }

    #[test]
    fn test_iter_descendants() {
        let tree = small();
        let mut iter = tree.root().descendants();

        assert_eq!(iter.next().unwrap().data(), &1);
        assert_eq!(iter.next().unwrap().data(), &11);
        assert_eq!(iter.next().unwrap().data(), &12);
        assert_eq!(iter.next().unwrap().data(), &121);
        assert_eq!(iter.next().unwrap().data(), &1211);
        assert_eq!(iter.next().unwrap().data(), &122);
        assert!(iter.next().is_none());
    }
}
