use crate::{BuildError, ErrorWith, Sapling, Tree, Vertex};
use std::convert::TryFrom;

#[derive(Debug, Clone)]
pub struct PolyTree<T, ASM = ()> {
    pub(crate) sap: Sapling<T, ASM>,
}

impl<T, ASM> PolyTree<T, ASM> {
    pub fn len(&self) -> usize {
        self.sap.len()
    }

    pub fn verts(&self) -> &[Vertex<T>] {
        self.sap.as_slice()
    }
}

impl<T, ASM> From<Tree<T, ASM>> for PolyTree<T, ASM> {
    fn from(tree: Tree<T, ASM>) -> Self {
        PolyTree { sap: tree.sap }
    }
}

impl<T, ASM> TryFrom<Sapling<T, ASM>> for PolyTree<T, ASM> {
    type Error = ErrorWith<BuildError, Sapling<T, ASM>>;

    fn try_from(sap: Sapling<T, ASM>) -> Result<Self, Self::Error> {
        match sap.can_build_polytree() {
            Ok(_) => Ok(PolyTree { sap }),
            Err(err) => Err(ErrorWith::new(err, sap)),
        }
    }
}
