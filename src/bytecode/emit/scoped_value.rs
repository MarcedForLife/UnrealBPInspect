//! Shared RAII guard for the emit layer's scoped thread-locals (the sequence
//! mask in `summary` and the inline-comment map in `comments`).
//!
//! Each thread-local owns its value (an `Option<T>` inside a `RefCell`).
//! [`ScopedValue::set`] moves a new value in, saving the previous binding, and
//! the guard moves the saved binding back on `Drop`. The `Drop`-based restore
//! survives a panic or early return inside the wrapped body, where a
//! hand-rolled set/restore pair would leave a stale value installed for
//! re-entrant emits. Storing the value by ownership keeps the consult path
//! free of raw pointers and `unsafe`.

use std::cell::RefCell;

/// RAII guard over a thread-local owned-value cell. On construction it installs
/// `value` and saves the previous binding; on `Drop` it restores the saved
/// binding.
pub(crate) struct ScopedValue<T: 'static> {
    key: &'static std::thread::LocalKey<RefCell<Option<T>>>,
    previous: Option<T>,
}

impl<T: 'static> ScopedValue<T> {
    /// Install `value` in `key`, returning a guard that restores the previous
    /// binding when dropped.
    pub(crate) fn set(
        key: &'static std::thread::LocalKey<RefCell<Option<T>>>,
        value: Option<T>,
    ) -> Self {
        let previous = key.with(|cell| cell.replace(value));
        ScopedValue { key, previous }
    }

    /// Run `consult` against the value currently installed in `key`. The value
    /// stays in the cell; only a borrow is exposed, so callers read without
    /// moving it out or cloning the whole value.
    pub(crate) fn with_current<R>(
        key: &'static std::thread::LocalKey<RefCell<Option<T>>>,
        consult: impl FnOnce(&T) -> R,
    ) -> Option<R> {
        key.with(|cell| cell.borrow().as_ref().map(consult))
    }
}

impl<T: 'static> Drop for ScopedValue<T> {
    fn drop(&mut self) {
        self.key
            .with(|cell| *cell.borrow_mut() = self.previous.take());
    }
}
