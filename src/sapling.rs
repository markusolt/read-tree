//! Builder for [`Tree`]s.

use crate::error::ErrorWith;
use crate::tree::{Node, PolyTree, Tree, Vertex};

/// Builder for [`Tree`]s.
///
/// *@TODO: Document `Sapling`*
#[derive(Debug, Clone)]
pub struct Sapling<T, ASM = ()> {
    open: Vec<usize>,
    assembly: Vec<ASM>,
    verts: Vec<Vertex<T>>,
}

impl<T> Sapling<T> {
    pub fn new() -> Self {
        Sapling::new_asm()
    }

    pub fn with_capacity(len: usize, depth: Option<usize>) -> Self {
        Sapling::with_capacity_asm(len, depth)
    }
}

impl<T, ASM> Sapling<T, ASM> {
    pub fn new_asm() -> Self {
        Sapling {
            open: Vec::new(),
            assembly: Vec::new(),
            verts: Vec::new(),
        }
    }

    pub fn with_capacity_asm(len: usize, depth: Option<usize>) -> Self {
        Sapling {
            open: Vec::with_capacity(depth.unwrap_or(0)),
            assembly: Vec::with_capacity(depth.unwrap_or(0)),
            verts: Vec::with_capacity(len),
        }
    }

    /// Removes all nodes from the sapling.
    pub fn clear(&mut self) {
        self.open.clear();
        self.assembly.clear();
        self.verts.clear();
    }

    /// Returns the number of nodes in the sapling.
    pub fn len(&self) -> usize {
        self.verts.len()
    }

    /// Returns `true` if there are `0` nodes in the sapling.
    pub fn is_empty(&self) -> bool {
        self.verts.is_empty()
    }

    /// Returns `true` if there are no open nodes in the sapling.
    pub fn is_complete(&self) -> bool {
        self.open.is_empty()
    }

    /// Attaches a new node to the sapling with the specified payload `data`.
    pub fn push(&mut self, data: T)
    where
        ASM: Default,
    {
        self.push_asm(data, ASM::default());
    }

    /// Attaches a new node to the sapling with the specified payload `data` and
    /// assembly information `asm`.
    pub fn push_asm(&mut self, data: T, asm: ASM) {
        self.open.push(self.verts.len());
        self.assembly.push(asm);
        self.verts.push(Vertex::new(data, 0));
    }

    /// Attaches a new node to the sapling and closes it immediately. The node
    /// will not have any [`Descendants`].
    ///
    /// [`Descendants`]: crate::Descendants
    pub fn push_leaf(&mut self, data: T) {
        self.verts.push(Vertex::new(data, 0));
    }

    /// Clones the nodes from the other tree into the sapling similar to
    /// [`push_leaf`]. Works best if `T` implements [`Copy`].
    ///
    /// Returns the consumed tree as an empty sapling.
    ///
    /// [`push_leaf`]: Sapling::push_leaf
    pub fn push_tree(&mut self, tree: Tree<T>) -> Sapling<T>
    where
        T: Clone,
    {
        let mut sap = Sapling::from(tree);
        self.verts.append(&mut sap.verts);
        sap.clear();
        sap
    }

    /// Clones the nodes from the other tree into the sapling similar to
    /// [`push_leaf`]. Works best if `T` implements [`Copy`].
    ///
    /// Returns the consumed tree as an empty sapling.
    ///
    /// [`push_leaf`]: Sapling::push_leaf
    pub fn push_polytree(&mut self, tree: PolyTree<T>) -> Sapling<T>
    where
        T: Clone,
    {
        let mut sap = Sapling::from(tree);
        self.verts.append(&mut sap.verts);
        sap.clear();
        sap
    }

    /// Clones the nodes from the other tree into the sapling similar to
    /// [`push_leaf`]. Works best if `T` implements [`Copy`].
    ///
    /// Returns the consumed tree as an empty sapling.
    ///
    /// [`push_leaf`]: Sapling::push_leaf
    pub fn push_node<'a>(&mut self, node: Node<'a, T>)
    where
        T: Clone,
    {
        self.verts.extend_from_slice(node.verts());
    }

    /// Returns a reference to the payload of the currently selected node.
    pub fn peek(&self) -> Option<&T> {
        Some(&self.verts[*self.open.last()?].data)
    }

    /// Returns references to the payload and assembly information of the
    /// currently selected node.
    pub fn peek_asm(&self) -> Option<(&T, &ASM)> {
        let i = *self.open.last()?;
        let asm = self.assembly.last().unwrap();

        Some((&self.verts[i].data, asm))
    }

    /// Returns a mutable reference to the payload of the currently selected
    /// node.
    pub fn peek_mut(&mut self) -> Option<&mut T> {
        Some(&mut self.verts[*self.open.last()?].data)
    }

    /// Returns mutable references to the payload and assembly information of
    /// the currently selected node.
    pub fn peek_asm_mut(&mut self) -> Option<(&mut T, &mut ASM)> {
        let i = *self.open.last()?;
        let asm = self.assembly.last_mut().unwrap();

        Some((&mut self.verts[i].data, asm))
    }

    /// Closes the currently selected node.
    ///
    /// Returns a mutable reference to the payload of the closed node.
    pub fn pop(&mut self) -> Option<&mut T> {
        let i = self.open.pop()?;
        self.assembly.pop().unwrap();

        self.verts[i].len = self.verts.len() - i - 1;
        Some(&mut self.verts[i].data)
    }

    /// Closes the currently selected node.
    ///
    /// Returns the assembly information of the closed node and a mutable
    /// reference to its payload.
    pub fn pop_asm(&mut self) -> Option<(&mut T, ASM)> {
        let i = self.open.pop()?;
        let asm = self.assembly.pop().unwrap();

        self.verts[i].len = self.verts.len() - i - 1;
        Some((&mut self.verts[i].data, asm))
    }

    /// Closes the currently selected node. Reassigns the descendants of the
    /// closed nodes to the parent of the closed node. This ensures the closed
    /// node has no [`Descendants`].
    ///
    /// Returns a mutable reference to the payload of the closed node.
    ///
    /// [`Descendants`]: crate::Descendants
    pub fn pop_as_leaf(&mut self) -> Option<&mut T> {
        let i = self.open.pop()?;
        self.assembly.pop().unwrap();

        Some(&mut self.verts[i].data)
    }

    /// Closes the currently selected node. Reassigns the descendants of the
    /// closed nodes to the parent of the closed node. This ensures the closed
    /// node has no [`Descendants`].
    ///
    /// Returns the assembly information of the closed node and a mutable
    /// reference to its payload.
    ///
    /// [`Descendants`]: crate::Descendants
    pub fn pop_as_leaf_asm(&mut self) -> Option<(&mut T, ASM)> {
        let i = self.open.pop()?;
        let asm = self.assembly.pop().unwrap();

        self.verts[i].len = self.verts.len() - i - 1;
        Some((&mut self.verts[i].data, asm))
    }

    /// Builds the sapling into a [`Tree`].
    ///
    /// Consumes the sapling in the process. On failure returns a [`BuildError`]
    /// containing the unmodified sapling.
    pub fn build(self) -> Result<Tree<T>, ErrorWith<BuildError, Sapling<T, ASM>>> {
        if self.is_empty() {
            return Err(ErrorWith::new(BuildError::Empty, self));
        }
        if !self.is_complete() {
            return Err(ErrorWith::new(BuildError::Incomplete, self));
        }
        if self.verts[0].len != self.verts.len() - 1 {
            return Err(ErrorWith::new(BuildError::MultipleRoots, self));
        }

        Ok(Tree {
            open: self.open,
            verts: self.verts,
        })
    }

    /// Builds the sapling into a [`PolyTree`].
    ///
    /// Consumes the sapling in the process. On failure returns a [`BuildError`]
    /// containing the unmodified sapling.
    pub fn build_polytree(self) -> Result<PolyTree<T>, ErrorWith<BuildError, Sapling<T, ASM>>> {
        if self.is_empty() {
            return Err(ErrorWith::new(BuildError::Empty, self));
        }
        if !self.is_complete() {
            return Err(ErrorWith::new(BuildError::Incomplete, self));
        }

        Ok(PolyTree {
            open: self.open,
            verts: self.verts,
        })
    }
}

impl<T> Default for Sapling<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> From<Tree<T>> for Sapling<T> {
    fn from(tree: Tree<T>) -> Self {
        Sapling {
            open: tree.open,
            assembly: Vec::new(),
            verts: tree.verts,
        }
    }
}

impl<T> From<PolyTree<T>> for Sapling<T> {
    fn from(tree: PolyTree<T>) -> Self {
        Sapling {
            open: tree.open,
            assembly: Vec::new(),
            verts: tree.verts,
        }
    }
}

impl<'a, T> From<Node<'a, T>> for Sapling<T>
where
    T: Clone,
{
    fn from(node: Node<'a, T>) -> Self {
        let mut sap = Sapling::new();
        sap.push_node(node);
        sap
    }
}

/// An error when building [`Sapling`]s into [`Tree`]s.
///
/// The error is usually returned inside a [`ErrorWith`]`<`[`BuildError`]`,
/// `[`Sapling`]<T, ASM>>`. This allows the caller of [`build`] to retake
/// ownership over the sapling when building fails.
///
/// [`build`]: Sapling::build
#[non_exhaustive]
#[derive(Debug)]
pub enum BuildError {
    /// The sapling is empty.
    Empty,

    /// The sapling contains open nodes.
    Incomplete,

    /// The sapling contains more than one root node.
    MultipleRoots,
}

impl fmt::Display for BuildError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Empty => write!(f, "The sapling is empty"),
            Self::Incomplete => write!(f, "The sapling contains unclosed nodes"),
            Self::MultipleRoots => write!(f, "The sapling contains more than one root node"),
        }
    }
}

impl std::error::Error for BuildError {}
