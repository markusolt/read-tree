//! General error types.

use std::error;
use std::fmt;

/// An error struct with an error and a payload.
///
/// When converting values it is necessary to return ownership of the original
/// value when an error occurs. This struct can be used to wrap an error `E` and
/// a payload `T` together to be used in a [`Result`]`<U, `[`ErrorWith`]`<E,
/// T>>`.
///
/// The struct implements [`Debug`], [`Display`] and [`Error`] as long as the
/// error type `E` implements them as well. The payload `T` does not need to
/// support any traits.
///
/// When the struct is printed it prints its payload `val: T` as `"val: [...]"`;
/// that is to say the value of type `T` is always printed as `[...]`. This
/// prevents filling the output with unwanted information and allows printing of
/// types `T` that do not implement [`Debug`].
///
/// Similarly [`Display`] is implemented to only include the value of `err: E`.1
///
/// # Examples
///
/// The following example tries to [`build`] a [`Sapling`] into a [`Tree`]. In
/// case of an error the sapling is returned unmodified using [`into_inner`].
///
/// ```rust,no_run
/// use read_tree::Sapling;
///
/// let mut sap = Sapling::<()>::new();
/// // [...]
///
/// // Try to build the sapling but return it as a sapling.
/// sap = match sap.build() {
///     Ok(tree) => {
///         println!("Sapling built successfully.");
///         tree.into()
///     }
///     Err(err_with) => {
///         println!("Sapling cannot be built: {}", err_with.err());
///         err_with.into_inner()
///     }
/// };
/// ```
///
/// [`build`]: crate::Sapling::build
/// [`Debug`]: fmt::Debug
/// [`Display`]: fmt::Display
/// [`Error`]: error::Error
/// [`into_inner`]: ErrorWith::into_inner
/// [`Sapling`]: crate::Sapling
/// [`Tree`]: crate::Tree
#[derive(Clone, Copy)]
pub struct ErrorWith<E, T> {
    pub err: E,
    pub val: T,
}

impl<E, T> ErrorWith<E, T> {
    /// Construct a new error with the error explanation `err` and the payload
    /// `val`.
    pub fn new(err: E, val: T) -> Self {
        ErrorWith { err, val }
    }

    /// Returns the `ErrorWith` with a new payload `val`.
    pub fn with(self, val: T) -> Self {
        ErrorWith { val, ..self }
    }

    /// Returns a reference to the error description.
    ///
    /// Usually error types implement [`Copy`], so no method for returning
    /// ownership of the `err` is provided.
    pub fn err(&self) -> &E {
        &self.err
    }

    /// Returns a reference to the payload.
    pub fn inner(&self) -> &T {
        &self.val
    }

    /// Returns a mutable reference to the payload.
    pub fn inner_mut(&mut self) -> &mut T {
        &mut self.val
    }

    /// Consumes the `ErrorWith` and returns ownership of the payload.
    ///
    /// # Examples
    ///
    /// The following example attempts to build a [`Sapling`] into a [`Tree`],
    /// then returns the original sapling. Notice that `sap` is moved into
    /// [`build`].
    ///
    /// ```rust
    /// use read_tree::Sapling;
    ///
    /// let mut sap = Sapling::<()>::new();
    /// sap = match sap.build() {
    ///     Ok(tree) => tree.into(),
    ///     Err(err) => err.into_inner(),
    /// }
    /// ```
    ///
    /// [`Sapling`]: crate::Sapling
    /// [`Tree`]: crate::Tree
    /// [`build`]: crate::Sapling::build
    pub fn into_inner(self) -> T {
        self.val
    }
}

impl<E, T> fmt::Debug for ErrorWith<E, T>
where
    E: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("ErrorWith")
            .field("err", &self.err)
            .field("val", &"[...]")
            .finish()
    }
}

impl<E, T> fmt::Display for ErrorWith<E, T>
where
    E: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.err)
    }
}

impl<E, T> error::Error for ErrorWith<E, T> where E: error::Error {}

/// An error when building [`Saplings`] into [`Trees`].
///
/// The error is usually contained in a [`ErrorWith`]`<`[`BuildError`]`,
/// `[`Sapling`]`<T, ASM>>`. The caller of methods like [`build`] can then
/// retake ownership over the sapling.
///
/// # Examples
///
/// ```rust
/// use read_tree::BuildError;
/// use read_tree::Sapling;
///
/// let mut sap = Sapling::<()>::new();
/// assert_eq!(sap.build().unwrap_err().err(), &BuildError::Empty);
///
/// let mut sap = Sapling::new();
/// sap.push(());
/// assert_eq!(sap.build().unwrap_err().err(), &BuildError::Incomplete);
///
/// let mut sap = Sapling::new();
/// sap.push_leaf(());
/// sap.push_leaf(());
/// assert_eq!(sap.build().unwrap_err().err(), &BuildError::MultipleRoots);
/// ```
///
/// [`build`]: Sapling::build
/// [`Saplings`]: Sapling
/// [`Trees`]: Tree
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum BuildError {
    /// The sapling is empty.
    Empty,

    /// The sapling contains open nodes.
    Incomplete,

    /// The sapling contains more than one root node.
    ///
    /// This error only occurs when attempting to [`build`] a sapling into a
    /// [`Tree`]. When this error occurs it is safe to build the sapling into a
    /// [`PolyTree`] instead. See [`build_polytree`].
    ///
    /// [`build_polytree`]: Sapling::build_polytree
    /// [`build`]: Sapling::build
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

/// An error returned when validating a vertex slice.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum ValidationError {
    /// The vertex slice is empty.
    ///
    /// Nodes must always have exactly one root. The buffer therefor needs to
    /// have at least one entry.
    Empty,

    /// The vertex slice contains more than one root node.
    ///
    /// Nodes can only have exactly one root node.
    MultipleRoots,

    /// Some of the lengths of the vertices do not match up. Ensure a vertex
    /// does not have more descendants than its ancestors.
    IllegalStructure,
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "Empty vertex slice"),
            Self::MultipleRoots => write!(f, "Multiple roots in vertex slice"),
            Self::IllegalStructure => write!(f, "Vertex with invalid length"),
        }
    }
}

impl std::error::Error for ValidationError {}
