use crate::{Branch, Node, PolyTree, Tree};

/// The [`Nodes`] that contain a particular node.
///
/// The ancestors of a node are its parent and the parents of its ancestors.
///
/// Ancestors of a node can be iterated over. The iteration begins with the
/// nodes parent and ends with the root of the [`Tree`]. The iteration supports
/// [`DoubleEndedIterator`]. Note that the reverse direction of the iterator is
/// significantly faster than the default direction. If the order of iteration
/// does not matter, [`rev`] should be used.
///
/// # Examples
///
/// ```rust
/// || -> Option<()> {
///     let tree = read_tree::demo::small_tree();
///     let mut ancestors = tree.get(5)?.ancestors();
///
///     assert_eq!(ancestors.next()?.data(), &122);
///     assert_eq!(ancestors.next()?.data(), &12);
///     assert_eq!(ancestors.next()?.data(), &1);
///
///     Some(())
/// }();
/// ```
///
/// [`Nodes`]: crate::Node
/// [`rev`]: Iterator::rev
/// [`Tree`]: crate::Tree
#[derive(Debug, Clone)]
pub struct Ancestors<'a, T> {
    /// The [`Index`] of the last yielded node from the front.
    ///
    /// [`Index`]: crate::vocab::Index
    front: usize,

    /// The [`Index`] of the next node that may be an ancestor to yield from the
    /// back.
    ///
    /// [`Index`]: crate::vocab::Index
    back: usize,
    branch: Branch<'a, T>,
}

impl<'a, T> From<Node<'a, T>> for Ancestors<'a, T> {
    fn from(node: Node<'a, T>) -> Self {
        Ancestors {
            front: node.index(),
            back: 0,
            branch: node.into(),
        }
    }
}

impl<'a, T> Iterator for Ancestors<'a, T> {
    type Item = Node<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.back >= self.front {
            return None;
        }

        for i in (self.back..self.front).rev() {
            if self.front <= i + self.branch.get(i).unwrap().len() {
                self.front = i;
                return self.branch.get(i);
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.back - self.front))
    }

    fn count(self) -> usize {
        // The reverse direction of the iterator can skip subtrees and is therefor
        // faster for most trees.
        self.rev().count()
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, T> DoubleEndedIterator for Ancestors<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let mut i = self.back;
        while i < self.front {
            let len = self.branch.get(i).unwrap().len();
            if i + len < self.front {
                i += len + 1;
            } else {
                self.back = i + 1;
                return self.branch.get(i);
            }
        }

        None
    }
}

/// The [`Nodes`] that have a particular node as a parent.
///
/// Children of a node can be iterated over. The iteration supports no special
/// qualities and implements [`size_hint`] poorly. Nonetheless it is a fast
/// iterator.
///
/// # Examples
///
/// ```rust
/// || -> Option<()> {
///     let tree = read_tree::demo::small_tree();
///     let mut children = tree.get(2)?.children();
///
///     assert_eq!(children.next()?.data(), &121);
///     assert_eq!(children.next()?.data(), &122);
///     assert_eq!(children.next()?.data(), &123);
///
///     Some(())
/// }();
/// ```
///
/// [`Nodes`]: crate::Node
/// [`size_hint`]: Iterator::size_hint
#[derive(Debug, Clone)]
pub struct Children<'a, T> {
    /// The [`Index`] of the next child node.
    ///
    /// [`Index`]: crate::vocab::Index
    front: usize,

    /// The [`Index`] of the first node beyond the iteration.
    ///
    /// [`Index`]: crate::vocab::Index
    back: usize,
    branch: Branch<'a, T>,
}

impl<'a, T, ASM> From<&'a PolyTree<T, ASM>> for Children<'a, T> {
    fn from(tree: &'a PolyTree<T, ASM>) -> Self {
        Children {
            front: 0,
            back: tree.len(),
            branch: tree.into(),
        }
    }
}

impl<'a, T> From<Node<'a, T>> for Children<'a, T> {
    fn from(node: Node<'a, T>) -> Self {
        Children {
            front: node.index() + 1,
            back: node.scope().end() + 1,
            branch: node.into(),
        }
    }
}

impl<'a, T> From<Branch<'a, T>> for Children<'a, T> {
    fn from(branch: Branch<'a, T>) -> Self {
        Children {
            front: 0,
            back: branch.len(),
            branch,
        }
    }
}

impl<'a, T> Iterator for Children<'a, T> {
    type Item = Node<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.front >= self.back {
            return None;
        }

        let ret = self.branch.get(self.front).unwrap();
        self.front += ret.len() + 1;
        Some(ret)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.front >= self.back {
            (0, Some(0))
        } else {
            (1, Some(self.back - self.front))
        }
    }
}

/// The [`Nodes`] of the subtree underneath a node.
///
/// The descendants of a node are its children and the children of its
/// descendants.
///
/// Descendants of a node can be iterated over depth first. The iteration
/// supports [`DoubleEndedIterator`] and [`ExactSizeIterator`].
///
/// # Examples
///
/// ```rust
/// || -> Option<()> {
///     let tree = read_tree::demo::small_tree();
///     let mut descendants = tree.get(2)?.descendants();
///
///     assert_eq!(descendants.next()?.data(), &121);
///     assert_eq!(descendants.next()?.data(), &122);
///     assert_eq!(descendants.next()?.data(), &1221);
///     assert_eq!(descendants.next()?.data(), &1222);
///     assert_eq!(descendants.next()?.data(), &123);
///
///     Some(())
/// }();
/// ```
///
/// [`Nodes`]: crate::Node
#[derive(Debug, Clone)]
pub struct Descendants<'a, T> {
    /// The [`Index`] of the next node to yield from the front.
    ///
    /// [`Index`]: crate::vocab::Index
    front: usize,

    /// The [`Index`] of the last yielded node from the back.
    ///
    /// [`Index`]: crate::vocab::Index
    back: usize,
    branch: Branch<'a, T>,
}

impl<'a, T, ASM> From<&'a Tree<T, ASM>> for Descendants<'a, T> {
    fn from(tree: &'a Tree<T, ASM>) -> Self {
        Descendants {
            front: 0,
            back: tree.len(),
            branch: tree.into(),
        }
    }
}

impl<'a, T, ASM> From<&'a PolyTree<T, ASM>> for Descendants<'a, T> {
    fn from(tree: &'a PolyTree<T, ASM>) -> Self {
        Descendants {
            front: 0,
            back: tree.len(),
            branch: tree.into(),
        }
    }
}

impl<'a, T> From<Node<'a, T>> for Descendants<'a, T> {
    fn from(node: Node<'a, T>) -> Self {
        Descendants {
            front: node.index() + 1,
            back: node.index() + node.len() + 1,
            branch: node.into(),
        }
    }
}

impl<'a, T> From<Branch<'a, T>> for Descendants<'a, T> {
    fn from(branch: Branch<'a, T>) -> Self {
        Descendants {
            front: 0,
            back: branch.len(),
            branch,
        }
    }
}

impl<'a, T> Iterator for Descendants<'a, T> {
    type Item = Node<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.front >= self.back {
            return None;
        }

        let ret = self.branch.get(self.front);
        self.front += 1;
        ret
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.front += n;
        self.next()
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }

    fn count(self) -> usize {
        self.len()
    }
}

impl<'a, T> DoubleEndedIterator for Descendants<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.front >= self.back {
            return None;
        }

        self.back -= 1;
        self.branch.get(self.back)
    }
}

impl<'a, T> ExactSizeIterator for Descendants<'a, T> {
    fn len(&self) -> usize {
        self.back - self.front
    }
}
