//! Opt-in per-comment placement audit (`BP_INSPECT_COMMENT_AUDIT`).
//!
//! Measurement only. The classifier records one [`PlacementTrace`] per comment
//! box/bubble describing which cascade strategy anchored it, the gate inputs
//! the heuristics keyed on, and the final placement or drop reason. When the
//! environment variable is set (to any non-empty value), the plan builder
//! prints a per-comment line plus an aggregate block to stderr. When unset,
//! nothing is printed and STDOUT is byte-identical with or without it.
//!
//! The trace never feeds STDOUT (summary/dump/json). It is collected on every
//! run but consumed only here, so correctness of the placement plan does not
//! depend on it.

use std::collections::BTreeMap;

/// The cascade strategy that anchored (or failed to anchor) one comment.
///
/// Bubble strategies cover a comment that sits on a single node; the remaining
/// strategies cover box comments. `Dropped` carries why the box never reached
/// a statement or header anchor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Strategy {
    /// Bubble anchored directly to its owner node's statement.
    BubbleDirect,
    /// Bubble anchored by following the owner's data-output pins.
    BubblePinFollow,
    /// Bubble anchored by following the owner's exec-output pins outward.
    BubbleExecFollow,
    /// Box promoted to an event-header annotation.
    EventWrapping,
    /// Box promoted to a whole-graph description below the signature.
    FunctionLevel,
    /// Box anchored to its top-left exec entry node's statement.
    InlineEntry,
    /// Box anchored to the first contained exec node that resolved.
    InlineFirstResolvable,
    /// Box anchored by walking exec-output links inside the contained set.
    ExecFollow,
    /// Box anchored by following data-output pins out of the contained set.
    PinFollow,
    /// Box on an ubergraph page anchored through the owner event's strict span.
    OwnerEventStrict,
    /// Box on an ubergraph page anchored through the per-range owner-event scan.
    OwnerEventPerRange,
    /// Box wanted a statement/header anchor but found none.
    Dropped(DropReason),
}

impl Strategy {
    /// Short stable tag for the per-comment line and the aggregate histogram.
    fn tag(self) -> &'static str {
        match self {
            Strategy::BubbleDirect => "bubble-direct",
            Strategy::BubblePinFollow => "bubble-pinfollow",
            Strategy::BubbleExecFollow => "bubble-execfollow",
            Strategy::EventWrapping => "event-wrapping",
            Strategy::FunctionLevel => "function-level",
            Strategy::InlineEntry => "inline-entry",
            Strategy::InlineFirstResolvable => "inline-first-resolvable",
            Strategy::ExecFollow => "exec-follow",
            Strategy::PinFollow => "pin-follow",
            Strategy::OwnerEventStrict => "owner-event-strict",
            Strategy::OwnerEventPerRange => "owner-event-per-range",
            Strategy::Dropped(_) => "dropped",
        }
    }
}

/// Why a box/bubble that wanted a statement or header anchor found none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DropReason {
    /// The comment carried no graph page, so it could not be placed at all.
    NoGraphPage,
    /// A box with no nodes inside its bounds.
    NoContainedNodes,
    /// The covering block had no byte map (inline placements cannot anchor).
    NoByteMap,
    /// A byte map existed but no statement covered the node's bytes.
    NoCoveringStatement,
    /// A pin-follow / exec-follow walk exhausted the reachable graph without
    /// reaching a covering statement.
    PinFollowDeadEnd,
    /// An ubergraph-page node resolved to no owning event body.
    OwnerEventUnresolved,
}

impl DropReason {
    /// Short stable tag for the drop-reason histogram.
    fn tag(self) -> &'static str {
        match self {
            DropReason::NoGraphPage => "no-graph-page",
            DropReason::NoContainedNodes => "no-contained-nodes",
            DropReason::NoByteMap => "no-byte-map",
            DropReason::NoCoveringStatement => "no-covering-statement",
            DropReason::PinFollowDeadEnd => "pin-follow-dead-end",
            DropReason::OwnerEventUnresolved => "owner-event-unresolved",
        }
    }
}

/// One audited comment outcome. Carried alongside the plan (never in STDOUT).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PlacementTrace {
    /// Graph page the comment came from (or `"<none>"` for a page-less box).
    pub page: String,
    /// Short snippet of the box text, for human scanning.
    pub snippet: String,
    pub strategy: Strategy,
    /// Identifiable nodes inside the box (the coverage numerator). `None` for
    /// bubbles, which own exactly one node rather than a contained set.
    pub contained: Option<usize>,
    /// Identifiable nodes on the page (the coverage denominator). `None` when
    /// no page total applies (bubbles, page-less boxes).
    pub page_total: Option<usize>,
    /// Follow depth actually used by pin-follow / exec-follow; `0` for direct
    /// and header anchors.
    pub depth: usize,
    /// Resolved `(block, statement_offset)` for inline placements, the block
    /// name for header placements, `None` for drops.
    pub placement: Option<(String, Option<usize>)>,
}

/// Truncate text to a single short snippet line for the per-comment audit row.
pub(crate) fn snippet_of(text: &str) -> String {
    const MAX: usize = 40;
    let flat = text.replace(['\n', '\r'], " ");
    let trimmed = flat.trim();
    if trimmed.chars().count() > MAX {
        let head: String = trimmed.chars().take(MAX).collect();
        format!("{head}...")
    } else {
        trimmed.to_string()
    }
}

/// Whether the placement audit is enabled for this run.
pub(crate) fn audit_enabled() -> bool {
    std::env::var_os("BP_INSPECT_COMMENT_AUDIT").is_some_and(|val| !val.is_empty())
}

/// Print the per-comment lines and the aggregate block to stderr when
/// `BP_INSPECT_COMMENT_AUDIT` is set. No-op otherwise.
pub(crate) fn maybe_emit_audit(traces: &[PlacementTrace]) {
    if !audit_enabled() {
        return;
    }
    eprintln!(
        "=== comment placement audit ({} comments) ===",
        traces.len()
    );
    for trace in traces {
        eprintln!("{}", format_trace_line(trace));
    }
    eprint!("{}", format_aggregate(traces));
}

/// Render one per-comment audit row: page, snippet, strategy, coverage, depth,
/// and the final placement or drop reason.
fn format_trace_line(trace: &PlacementTrace) -> String {
    let coverage = match (trace.contained, trace.page_total) {
        (Some(contained), Some(total)) => format!("{contained}/{total}"),
        (Some(contained), None) => format!("{contained}/-"),
        _ => "-".to_string(),
    };
    let outcome = match (&trace.placement, trace.strategy) {
        (Some((block, Some(offset))), _) => format!("-> {block}@0x{offset:x}"),
        (Some((block, None)), _) => format!("-> {block} (header)"),
        (None, Strategy::Dropped(reason)) => format!("DROP {}", reason.tag()),
        (None, _) => "DROP".to_string(),
    };
    format!(
        "[{page}] {strategy:<22} cov={coverage:<7} depth={depth} {outcome}  \"{snippet}\"",
        page = trace.page,
        strategy = trace.strategy.tag(),
        depth = trace.depth,
        snippet = trace.snippet,
    )
}

/// Render the aggregate block: counts per strategy, drop-reason histogram,
/// coverage-ratio distribution, and the maximum follow depth observed.
fn format_aggregate(traces: &[PlacementTrace]) -> String {
    let mut strategy_counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut drop_counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut coverage_ratios: Vec<f64> = Vec::new();
    let mut max_depth = 0usize;
    let mut dropped_total = 0usize;
    for trace in traces {
        *strategy_counts.entry(trace.strategy.tag()).or_insert(0) += 1;
        if let Strategy::Dropped(reason) = trace.strategy {
            *drop_counts.entry(reason.tag()).or_insert(0) += 1;
            dropped_total += 1;
        }
        if let (Some(contained), Some(total)) = (trace.contained, trace.page_total) {
            if total > 0 {
                coverage_ratios.push(contained as f64 / total as f64);
            }
        }
        max_depth = max_depth.max(trace.depth);
    }

    let mut out = String::new();
    out.push_str("--- aggregate ---\n");
    out.push_str(&format!("total comments: {}\n", traces.len()));
    out.push_str("strategy counts:\n");
    for (tag, count) in &strategy_counts {
        out.push_str(&format!("  {tag:<24} {count}\n"));
    }
    out.push_str(&format!("dropped: {dropped_total}\n"));
    if drop_counts.is_empty() {
        out.push_str("drop reasons: none\n");
    } else {
        out.push_str("drop reasons:\n");
        for (tag, count) in &drop_counts {
            out.push_str(&format!("  {tag:<24} {count}\n"));
        }
    }
    out.push_str(&format!("max follow depth: {max_depth}\n"));
    out.push_str(&coverage_distribution(&mut coverage_ratios));
    out
}

/// Coverage-ratio shape: count, min/median/max, and a coarse decile histogram.
/// Mutates the input by sorting it in place.
fn coverage_distribution(ratios: &mut [f64]) -> String {
    if ratios.is_empty() {
        return "coverage ratios: none (no box with a page total)\n".to_string();
    }
    ratios.sort_by(|a, b| a.partial_cmp(b).expect("coverage ratios are finite"));
    let count = ratios.len();
    let min = ratios[0];
    let max = ratios[count - 1];
    let median = ratios[count / 2];
    let mut histogram = [0usize; 10];
    for &ratio in ratios.iter() {
        // Clamp 1.0 (full coverage) into the top bucket rather than overflowing.
        let bucket = ((ratio * 10.0) as usize).min(9);
        histogram[bucket] += 1;
    }
    let mut out = String::new();
    out.push_str(&format!(
        "coverage ratios: count={count} min={min:.2} median={median:.2} max={max:.2}\n"
    ));
    out.push_str("coverage histogram (decile buckets):\n");
    for (index, &bucket_count) in histogram.iter().enumerate() {
        let low = index as f64 / 10.0;
        let high = (index + 1) as f64 / 10.0;
        out.push_str(&format!("  [{low:.1},{high:.1}) {bucket_count}\n"));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn trace(strategy: Strategy, contained: Option<usize>, total: Option<usize>) -> PlacementTrace {
        PlacementTrace {
            page: "P".into(),
            snippet: "s".into(),
            strategy,
            contained,
            page_total: total,
            depth: 0,
            placement: None,
        }
    }

    #[test]
    fn snippet_truncates_and_flattens() {
        assert_eq!(snippet_of("  hello\nworld  "), "hello world");
        let long = "x".repeat(60);
        let snippet = snippet_of(&long);
        assert!(snippet.ends_with("..."));
        assert_eq!(snippet.chars().count(), 43);
    }

    #[test]
    fn aggregate_counts_strategies_and_drops() {
        let traces = vec![
            trace(Strategy::FunctionLevel, Some(4), Some(4)),
            trace(Strategy::Dropped(DropReason::NoByteMap), Some(1), Some(4)),
            trace(Strategy::Dropped(DropReason::NoByteMap), None, None),
        ];
        let aggregate = format_aggregate(&traces);
        assert!(aggregate.contains("function-level           1"));
        assert!(aggregate.contains("dropped: 2"));
        assert!(aggregate.contains("no-byte-map              2"));
        assert!(aggregate.contains("max follow depth: 0"));
        // Two coverage ratios contributed (the page-less drop has no total).
        assert!(aggregate.contains("count=2"));
    }

    #[test]
    fn coverage_distribution_buckets_full_coverage_into_top() {
        let mut ratios = vec![1.0, 0.25];
        let out = coverage_distribution(&mut ratios);
        assert!(out.contains("[0.9,1.0) 1"));
        assert!(out.contains("[0.2,0.3) 1"));
    }
}
