use crate::{BuildError, ErrorWith, Node, PolyTree, Sapling, ValidationError, Vertex};
use std::convert::{TryFrom, TryInto};

#[derive(Debug, Clone)]
pub struct Tree<T, ASM = ()> {
    pub(crate) sap: Sapling<T, ASM>,
}

impl<T> Tree<T> {
    pub fn from_vec(
        vec: Vec<Vertex<T>>,
    ) -> Result<Self, ErrorWith<ValidationError, Vec<Vertex<T>>>> {
        vec.try_into()
    }

    pub unsafe fn from_vec_unchecked(vec: Vec<Vertex<T>>) -> Self {
        Tree {
            sap: Sapling {
                open: Vec::new(),
                verts: vec,
            },
        }
    }
}

impl<T, ASM> Tree<T, ASM> {
    pub fn as_node(&self) -> Node<T> {
        Node {
            index: 0,
            verts: self.as_slice(),
        }
    }

    pub fn as_slice(&self) -> &[Vertex<T>] {
        self.sap.as_slice()
    }

    pub fn len(&self) -> usize {
        self.sap.len()
    }

    pub fn get(&self, index: usize) -> Option<Node<T>> {
        if index >= self.sap.len() {
            return None;
        }

        Some(Node {
            index,
            verts: self.as_slice(),
        })
    }
}

impl<'a, T> From<Node<'a, T>> for Tree<T>
where
    T: Clone,
{
    fn from(node: Node<'a, T>) -> Self {
        let mut sap = Sapling::new();
        sap.push_node(node);
        Tree { sap }
    }
}

impl<T, ASM> TryFrom<Sapling<T, ASM>> for Tree<T, ASM> {
    type Error = ErrorWith<BuildError, Sapling<T, ASM>>;

    fn try_from(sap: Sapling<T, ASM>) -> Result<Self, Self::Error> {
        match sap.can_build() {
            Ok(_) => Ok(Tree { sap }),
            Err(err) => Err(ErrorWith::new(err, sap)),
        }
    }
}

impl<T, ASM> TryFrom<PolyTree<T, ASM>> for Tree<T, ASM> {
    type Error = ErrorWith<ValidationError, PolyTree<T, ASM>>;

    fn try_from(tree: PolyTree<T, ASM>) -> Result<Self, Self::Error> {
        if tree.verts()[0].len < tree.verts().len() - 1 {
            return Err(ErrorWith::new(ValidationError::MultipleRoots, tree));
        }

        Ok(Tree { sap: tree.sap })
    }
}

impl<T> TryFrom<Vec<Vertex<T>>> for Tree<T> {
    type Error = ErrorWith<ValidationError, Vec<Vertex<T>>>;

    fn try_from(vec: Vec<Vertex<T>>) -> Result<Self, Self::Error> {
        match Node::try_from(&vec[..]) {
            Ok(_) => Ok(unsafe { Tree::from_vec_unchecked(vec) }),
            Err(err) => Err(ErrorWith::new(err, vec)),
        }
    }
}
