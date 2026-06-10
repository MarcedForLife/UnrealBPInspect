//! Decoded-asset container types for the decode pipeline.
//!
//! A fully decoded Blueprint (Unreal Blueprint) asset is represented as
//! separate vectors of `Function` and `Event` entries rather than a flat
//! map, because functions and events carry distinct metadata in the editor
//! (function signature vs event kind) and downstream consumers (emit, call
//! graph, pin hints) need that distinction.

use std::collections::BTreeMap;

use crate::bytecode::stmt::Stmt;

/// The decoded representation of a single Blueprint asset.
#[derive(serde::Serialize, serde::Deserialize)]
pub struct DecodedAsset {
    pub functions: Vec<Function>,
    pub events: Vec<Event>,
    /// Latent-call resume continuations, keyed by the originating call's
    /// disk offset (the `Stmt::Call.offset` carried through transform
    /// and emit). The emitter looks up this map when rendering a Call
    /// at one of the recognised latent function names (`Delay`,
    /// `MoveComponentTo`, etc.) and interleaves the resume body inline
    /// after the call line. Empty for assets without latent calls.
    #[serde(default)]
    pub resume_bodies: BTreeMap<usize, Vec<Stmt>>,
}

/// A decoded Blueprint function.
#[derive(serde::Serialize, serde::Deserialize)]
pub struct Function {
    pub name: String,
    pub body: Vec<Stmt>,
    /// 1-based package export index this body was decoded from, used to key
    /// the body back to its export in `dump_bridge`. `None` only for synthetic
    /// test constructors. `skip_serializing_if` keeps the JSON form identical
    /// to assets decoded before this field existed.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub export_index: Option<usize>,
}

/// A decoded Blueprint event entry point.
#[derive(serde::Serialize, serde::Deserialize)]
pub struct Event {
    pub name: String,
    pub body: Vec<Stmt>,
    /// 1-based package export index of the event's stub function export (the
    /// export whose bytecode dispatches into the ubergraph). `None` only for
    /// synthetic test constructors. See [`Function::export_index`].
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub export_index: Option<usize>,
}
