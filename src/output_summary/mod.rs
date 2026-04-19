//! Summary output mode (default).
//!
//! EdGraph comments are placed inline near corresponding bytecode using pin-based
//! structural analysis (exec entry points, BFS ownership) with spatial fallback.

mod call_graph;
mod comments;
mod edgraph;
mod filter;
mod format;
mod ubergraph;

pub use filter::filter_summary;
pub use format::format_summary;

use std::collections::HashSet;
use std::fmt::Write;

#[derive(Clone)]
struct CommentBox {
    text: String,
    x: i32,
    y: i32,
    width: i32,
    height: i32,
    is_bubble: bool,
    /// EdGraph page this comment belongs to (e.g. "EventGraph", "BeginPlay").
    graph_page: String,
    /// For bubble comments: 1-based export index of the owning node.
    /// Allows direct lookup via pin data instead of spatial proximity.
    owner_export: usize,
}

impl CommentBox {
    fn contains_point(&self, px: i32, py: i32) -> bool {
        px >= self.x && py >= self.y && px <= self.x + self.width && py <= self.y + self.height
    }
}

#[derive(Clone)]
struct NodeInfo {
    x: i32,
    y: i32,
    identifier: String,
    /// Pure nodes (VariableGet) have no execution pins and produce expressions
    /// inlined into other statements. Their identifiers appear at multiple
    /// bytecode locations, making rank-based matching unreliable for box comments.
    is_pure: bool,
    /// True for K2Node_VariableSet nodes. Assignment lines (`self.X = ...`) are
    /// matched instead of any reference, preventing false matches on read-only usage.
    is_variable_set: bool,
    /// 1-based export index in the asset, used for pin-based event ownership lookup.
    export_index: usize,
    /// EdGraph page this node belongs to.
    graph_page: String,
}

struct UbergraphSection {
    name: String,
    lines: Vec<String>,
}

impl UbergraphSection {
    fn is_event(&self) -> bool {
        !self.name.is_empty() && self.name != LATENT_RESUME_SECTION
    }
}

struct ResumeBlock {
    lines: Vec<String>,
}

/// Synthetic identifier for K2Node_IfThenElse (Branch) nodes.
const BRANCH_IDENTIFIER: &str = "__branch__";

/// Section name for latent resume blocks in the ubergraph.
const LATENT_RESUME_SECTION: &str = "(latent resume)";

const COMMENT_WRAP_WIDTH: usize = 100;
const MAX_BUBBLE_DISTANCE_SQ: i64 = 640_000; // 800px squared
const OFFSET_PREFIX_LEN: usize = "0000: ".len();

/// Strip the hex offset prefix from a bytecode line (e.g. `0012: expr` -> `expr`).
fn strip_offset_prefix(line: &str) -> &str {
    if line.len() > OFFSET_PREFIX_LEN && line.as_bytes()[4] == b':' {
        &line[OFFSET_PREFIX_LEN..]
    } else {
        line
    }
}

/// Emit a blank line separator between consecutive sections.
fn section_sep(buf: &mut String, count: &mut usize) {
    if *count > 0 {
        writeln!(buf).unwrap();
    }
    *count += 1;
}

fn emit_comment(buf: &mut String, text: &str, indent: &str) {
    let prefix = format!("{}// ", indent);
    let avail = COMMENT_WRAP_WIDTH.saturating_sub(prefix.len() + 1);
    for paragraph in text.lines() {
        let para = paragraph.trim();
        if para.is_empty() {
            continue;
        }
        let mut wrapped: Vec<String> = Vec::new();
        let mut cur = String::new();
        for word in para.split_whitespace() {
            if cur.is_empty() {
                cur = word.to_string();
            } else if cur.len() + 1 + word.len() <= avail {
                cur.push(' ');
                cur.push_str(word);
            } else {
                wrapped.push(cur);
                cur = word.to_string();
            }
        }
        if !cur.is_empty() {
            wrapped.push(cur);
        }
        match wrapped.len() {
            0 => {}
            1 => writeln!(buf, "{}\"{}\"", prefix, wrapped[0]).unwrap(),
            n => {
                writeln!(buf, "{}\"{}", prefix, wrapped[0]).unwrap();
                for (i, segment) in wrapped.iter().enumerate().skip(1) {
                    if i == n - 1 {
                        writeln!(buf, "{} {}\"", prefix, segment).unwrap();
                    } else {
                        writeln!(buf, "{} {}", prefix, segment).unwrap();
                    }
                }
            }
        }
    }
}

fn strip_node_func_prefix(name: &str) -> String {
    name.strip_prefix("K2_")
        .or_else(|| name.strip_prefix("Conv_"))
        .or_else(|| name.strip_prefix("Array_"))
        .unwrap_or(name)
        .to_string()
}

fn find_local_calls(line: &str, local_fns: &HashSet<String>) -> Vec<String> {
    let mut found = Vec::new();
    for func in local_fns {
        let pattern = format!("{}(", func);
        if let Some(pos) = line.find(&pattern) {
            let is_boundary = pos == 0 || {
                let prev = line.as_bytes()[pos - 1];
                !(prev.is_ascii_alphanumeric() || prev == b'_' || prev == b'.')
            };
            if is_boundary {
                found.push(func.clone());
            }
        }
    }
    found
}

/// Strip `/*resume:0xHEX*/` annotations from a line for display.
fn strip_resume_annotation(line: &str) -> String {
    if let Some(start) = line.find(" /*resume:0x") {
        if let Some(end) = line[start..].find("*/") {
            return format!("{}{}", &line[..start], &line[start + end + 2..]);
        }
    }
    line.to_string()
}
