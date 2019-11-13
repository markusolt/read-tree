use crate::{Node, PolyTree, Tree, ValidationError, Vertex};
use std::convert::{TryFrom, TryInto};

#[derive(Debug)]
pub struct Branch<'a, T> {
    verts: &'a [Vertex<T>],
}

impl<'a, T> Branch<'a, T> {
    pub fn from_slice(slice: &'a [Vertex<T>]) -> Result<Self, ValidationError> {
        slice.try_into()
    }

    pub unsafe fn from_slice_unchecked(slice: &'a [Vertex<T>]) -> Self {
        Branch { verts: slice }
    }

    pub fn verts(self) -> &'a [Vertex<T>] {
        &self.verts[..]
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

impl<'a, T, ASM> From<&'a Tree<T, ASM>> for Branch<'a, T> {
    fn from(tree: &'a Tree<T, ASM>) -> Self {
        Branch {
            verts: tree.sap.verts(),
        }
    }
}

impl<'a, T, ASM> From<&'a PolyTree<T, ASM>> for Branch<'a, T> {
    fn from(tree: &'a PolyTree<T, ASM>) -> Self {
        Branch {
            verts: tree.sap.verts(),
        }
    }
}

impl<'a, T> From<Node<'a, T>> for Branch<'a, T> {
    fn from(node: Node<'a, T>) -> Self {
        Branch {
            verts: node.verts(),
        }
    }
}

impl<'a, T> TryFrom<&'a [Vertex<T>]> for Branch<'a, T> {
    type Error = ValidationError;

    fn try_from(slice: &'a [Vertex<T>]) -> Result<Self, Self::Error> {
        if slice.is_empty() {
            return Err(ValidationError::Empty);
        }

        let mut open = Vec::new();
        for (i, val) in slice.iter().enumerate() {
            while open.last() == Some(&i) {
                open.pop().ok_or(ValidationError::IllegalStructure)?;
            }

            let scope = i + val.len + 1;
            if open.last().map(|head| *head < scope) == Some(true) {
                return Err(ValidationError::IllegalStructure);
            }
            open.push(scope);
        }

        Ok(Branch { verts: slice })
    }
}

impl<'a, T> Copy for Branch<'a, T> {}

impl<'a, T> Clone for Branch<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}
