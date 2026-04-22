//! Thread-local scope for pin-derived branch hints.
//!
//! The summary pipeline builds `BranchHints` and `BytecodeBranchMap` from
//! the full `ParsedAsset`, but the downstream CFG-based else-branch
//! detector runs deep inside per-export bytecode structuring where those
//! values are not naturally in scope. Threading them through every
//! structurer entry point would touch many signatures, so we stash them
//! in a thread-local cell for the duration of the summary pipeline.
//!
//! Usage:
//! - `install(hints, map)` at the top of the pipeline before structuring.
//! - `with(|scope| ...)` deep inside structuring to consult the scope.
//! - `clear()` once the pipeline finishes, or use `Guard` for RAII.
//!
//! The cell is thread-local and single-threaded, so `RefCell<Option<...>>`
//! suffices; no `Arc` or `Mutex` is needed for a CLI.

use std::cell::RefCell;

use crate::pin_hints::{BranchHints, BytecodeBranchMap};

thread_local! {
    static SCOPE: RefCell<Option<(BranchHints, BytecodeBranchMap)>> = const { RefCell::new(None) };
    static CURRENT_FUNCTION_KEY: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Run `body` with `key` installed as the current function key on the
/// thread-local. Restores the previous key (typically `None`) on return.
/// Callers near the per-event emission site use this so the else-branch
/// detector can consult pin hints without threading the key through every
/// intermediate signature.
pub fn with_function_key<R>(key: &str, body: impl FnOnce() -> R) -> R {
    let previous = CURRENT_FUNCTION_KEY.with(|slot| slot.borrow_mut().replace(key.to_string()));
    let result = body();
    CURRENT_FUNCTION_KEY.with(|slot| *slot.borrow_mut() = previous);
    result
}

/// Read the current function key, if any. Returns `None` when no key is
/// installed (e.g. raw bytecode tests).
pub fn current_function_key() -> Option<String> {
    CURRENT_FUNCTION_KEY.with(|slot| slot.borrow().clone())
}

/// Install hints and map into the thread-local scope. Panics if a scope
/// is already installed on this thread, which would indicate overlapping
/// pipeline invocations or a missing `clear()`.
pub fn install(hints: BranchHints, map: BytecodeBranchMap) {
    SCOPE.with(|slot| {
        let mut borrow = slot.borrow_mut();
        assert!(
            borrow.is_none(),
            "pin_hints_scope already installed; call clear() first"
        );
        *borrow = Some((hints, map));
    });
}

/// Run `f` with read-only access to the current scope. The closure
/// receives `None` when no scope is installed (e.g. raw bytecode tests
/// that bypass the summary pipeline).
pub fn with<R>(f: impl FnOnce(Option<&(BranchHints, BytecodeBranchMap)>) -> R) -> R {
    SCOPE.with(|slot| f(slot.borrow().as_ref()))
}

/// Tear down the scope. Safe to call when no scope is installed.
pub fn clear() {
    SCOPE.with(|slot| {
        *slot.borrow_mut() = None;
    });
}

/// RAII guard that installs on construction and clears on drop. Prefer
/// this over raw `install`/`clear` pairs in pipelines with early returns
/// or `?` propagation, to avoid leaving stale scope on failure paths.
pub struct Guard;

impl Guard {
    pub fn new(hints: BranchHints, map: BytecodeBranchMap) -> Self {
        install(hints, map);
        Self
    }
}

impl Drop for Guard {
    fn drop(&mut self) {
        clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn empty_pair() -> (BranchHints, BytecodeBranchMap) {
        (BranchHints::default(), BytecodeBranchMap::default())
    }

    #[test]
    fn with_returns_none_when_empty() {
        // Ensure prior tests on this thread didn't leak state.
        clear();
        let observed = with(|scope| scope.is_some());
        assert!(!observed, "scope should be empty initially");
    }

    #[test]
    fn install_and_with_round_trip() {
        clear();
        let (hints, map) = empty_pair();
        install(hints, map);
        let observed = with(|scope| scope.is_some());
        assert!(observed, "scope should be visible after install");
        clear();
    }

    #[test]
    fn clear_removes_scope() {
        clear();
        let (hints, map) = empty_pair();
        install(hints, map);
        clear();
        let observed = with(|scope| scope.is_some());
        assert!(!observed, "scope should be empty after clear");
    }

    #[test]
    #[should_panic(expected = "pin_hints_scope already installed")]
    fn double_install_panics() {
        clear();
        let (hints1, map1) = empty_pair();
        install(hints1, map1);
        let (hints2, map2) = empty_pair();
        install(hints2, map2); // should panic
    }

    #[test]
    fn guard_clears_on_drop() {
        clear();
        let (hints, map) = empty_pair();
        {
            let _guard = Guard::new(hints, map);
            assert!(with(|scope| scope.is_some()));
        }
        assert!(!with(|scope| scope.is_some()));
    }
}
