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
