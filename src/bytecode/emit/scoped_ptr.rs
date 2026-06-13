//! Shared RAII guard for the emit layer's scoped thread-local pointers
//! (the sequence mask in `summary` and the inline-comment map in `comments`).

use std::cell::RefCell;

/// RAII guard over a thread-local raw-pointer cell. On construction it
/// installs `value` and saves the previous binding; on `Drop` it restores
/// the saved binding. The `Drop`-based restore closes the latent hole the
/// hand-rolled set/restore pairs left open: a panic or early return inside
/// the wrapped body would otherwise skip the restore and leave a stale
/// pointer installed for re-entrant emits.
pub(crate) struct ScopedPtr<T: 'static> {
    key: &'static std::thread::LocalKey<RefCell<Option<*const T>>>,
    previous: Option<*const T>,
}

impl<T: 'static> ScopedPtr<T> {
    /// Install `value` in `key`, returning a guard that restores the
    /// previous binding when dropped.
    pub(crate) fn set(
        key: &'static std::thread::LocalKey<RefCell<Option<*const T>>>,
        value: Option<*const T>,
    ) -> Self {
        let previous = key.with(|cell| cell.replace(value));
        ScopedPtr { key, previous }
    }

    /// The pointer currently installed in `key`, or `None`.
    pub(crate) fn get(
        key: &'static std::thread::LocalKey<RefCell<Option<*const T>>>,
    ) -> Option<*const T> {
        key.with(|cell| *cell.borrow())
    }
}

impl<T: 'static> Drop for ScopedPtr<T> {
    fn drop(&mut self) {
        self.key.with(|cell| *cell.borrow_mut() = self.previous);
    }
}
