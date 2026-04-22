//! Section-boundary, resume-map, and section-body emission.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::bytecode::BARE_RETURN;
use crate::helpers::indent_of;
use crate::types::NodePinData;

use super::super::edgraph::EdGraphData;
use super::super::{
    emit_comment, section_sep, strip_resume_annotation, CommentBox, NodeInfo, ResumeBlock,
    UbergraphSection, LATENT_RESUME_SECTION,
};

use super::comment_placement::{build_ubergraph_comment_ctx, UbergraphCommentCtx};
use super::events::{clean_event_header, compute_action_key_events, resolve_event_position};
use super::linearize::split_ubergraph_sections;

/// Extract `/*resume:0xHEX*/` offset from a bytecode line.
fn parse_resume_offset(line: &str) -> Option<usize> {
    let marker = line.find("/*resume:0x")?;
    let hex_start = marker + 11;
    let hex_end = line[hex_start..].find("*/")? + hex_start;
    usize::from_str_radix(&line[hex_start..hex_end], 16).ok()
}

/// Pair each `/*resume:0xHEX*/` annotation with a resume block, in order.
fn build_delay_resume_map(
    sections: &[UbergraphSection],
    resume_count: usize,
) -> Vec<(usize, usize)> {
    let mut map: Vec<(usize, usize)> = Vec::new();
    let mut resume_idx = 0usize;
    for (si, section) in sections.iter().enumerate() {
        if !section.is_event() {
            continue;
        }
        for line in &section.lines {
            if parse_resume_offset(line).is_some() && resume_idx < resume_count {
                map.push((si, resume_idx));
                resume_idx += 1;
            }
        }
    }
    map
}

/// Map full-output line indices to event section names.
fn build_section_boundaries(lines: &[String]) -> Vec<(usize, String)> {
    lines
        .iter()
        .enumerate()
        .filter_map(|(i, line)| {
            let trimmed = line.trim();
            if trimmed.starts_with("--- ") && trimmed.ends_with(" ---") {
                let name = &trimmed[4..trimmed.len() - 4];
                if !name.is_empty() && name != LATENT_RESUME_SECTION {
                    return Some((i + 1, name.to_string()));
                }
            }
            None
        })
        .collect()
}

/// Emit bytecode lines with interleaved inline comments and resume blocks.
fn emit_section_body(
    buf: &mut String,
    section: &UbergraphSection,
    inline_comments: &[(usize, &CommentBox)],
    resume_blocks: &[ResumeBlock],
    section_resumes: &[usize],
    body_indent: &str,
) {
    let mut resume_pos = 0;
    let mut inline_idx = 0;
    for (i, line) in section.lines.iter().enumerate() {
        while inline_idx < inline_comments.len() && inline_comments[inline_idx].0 == i {
            let ws_len = indent_of(line);
            let indent = format!("{}{}", body_indent, &line[..ws_len]);
            emit_comment(buf, &inline_comments[inline_idx].1.text, &indent);
            inline_idx += 1;
        }

        let clean = strip_resume_annotation(line);
        if clean.trim() == BARE_RETURN {
            continue;
        }
        writeln!(buf, "{}{}", body_indent, clean).unwrap();

        if parse_resume_offset(line).is_some() && resume_pos < section_resumes.len() {
            if let Some(rb) = resume_blocks.get(section_resumes[resume_pos]) {
                for rline in &rb.lines {
                    writeln!(buf, "{}{}", body_indent, rline).unwrap();
                }
            }
            resume_pos += 1;
        }
    }
}

/// Split ubergraph structured output into per-event sections and inline latent resumes.
pub(in crate::output_summary) fn emit_ubergraph_events(
    buf: &mut String,
    lines: &[String],
    comments: Option<&[CommentBox]>,
    nodes: Option<&[NodeInfo]>,
    edgraph: &EdGraphData,
    pin_data: &HashMap<usize, NodePinData>,
    callers_map: &HashMap<String, Vec<String>>,
) {
    let (sections, resume_blocks) = split_ubergraph_sections(lines);
    let delay_resume_map = build_delay_resume_map(&sections, resume_blocks.len());

    let section_boundaries = build_section_boundaries(lines);
    let boundary_refs: Vec<(usize, &str)> = section_boundaries
        .iter()
        .map(|(i, name)| (*i, name.as_str()))
        .collect();

    let ctx = if let Some(cbs) = comments {
        build_ubergraph_comment_ctx(
            cbs,
            nodes.unwrap_or(&[]),
            lines,
            &boundary_refs,
            &sections,
            edgraph,
            pin_data,
        )
    } else {
        UbergraphCommentCtx {
            small_group_idxs: HashSet::new(),
            section_inline: HashMap::new(),
            section_wrapping: HashMap::new(),
        }
    };

    let mut section_resume_map: HashMap<usize, Vec<usize>> = HashMap::new();
    for &(si, ri) in &delay_resume_map {
        section_resume_map.entry(si).or_default().push(ri);
    }

    let section_names: Vec<&str> = sections.iter().map(|s| s.name.as_str()).collect();
    let action_key_events = compute_action_key_events(&section_names);

    let mut emitted_group_comments: HashSet<usize> = HashSet::new();
    let mut emitted_event_count = 0usize;

    for (si, section) in sections.iter().enumerate() {
        if !section.is_event() {
            continue;
        }
        if section.name.is_empty() {
            let has_content = section.lines.iter().any(|l| {
                let trimmed = l.trim();
                !trimmed.is_empty() && trimmed != "return"
            });
            if !has_content {
                continue;
            }
        }

        section_sep(buf, &mut emitted_event_count);

        let (sig_indent, body_indent) = (super::super::INDENT, super::super::BODY_INDENT);

        let empty_wrapping: Vec<&CommentBox> = Vec::new();
        let empty_inline: Vec<(usize, &CommentBox)> = Vec::new();
        let top_level = ctx
            .section_wrapping
            .get(&section.name)
            .unwrap_or(&empty_wrapping);
        let inline = ctx
            .section_inline
            .get(&section.name)
            .unwrap_or(&empty_inline);

        // Header: group comments, callers, wrapping comments, signature.
        if !section.name.is_empty() {
            if let Some(cbs) = comments {
                let event_pos = resolve_event_position(
                    &section.name,
                    &edgraph.event_positions,
                    &edgraph.input_action_positions,
                );
                if let Some((ex, ey, ref page)) = event_pos {
                    for (i, cb) in cbs.iter().enumerate() {
                        if ctx.small_group_idxs.contains(&i)
                            && !emitted_group_comments.contains(&i)
                            && cb.graph_page == *page
                            && cb.contains_point(ex, ey)
                        {
                            emit_comment(buf, &cb.text, super::super::INDENT);
                            emitted_group_comments.insert(i);
                        }
                    }
                }
            }
            if let Some(callers) = callers_map.get(&section.name) {
                writeln!(buf, "{}// called by: {}", sig_indent, callers.join(", ")).unwrap();
            }
            for cb in top_level {
                emit_comment(buf, &cb.text, sig_indent);
            }
            let display_name = clean_event_header(&section.name, &action_key_events);
            if display_name.contains('(') {
                writeln!(buf, "{}{}:", sig_indent, display_name).unwrap();
            } else {
                writeln!(buf, "{}{}():", sig_indent, display_name).unwrap();
            }
        }

        let section_resumes = section_resume_map
            .get(&si)
            .map(|v| v.as_slice())
            .unwrap_or(&[]);
        emit_section_body(
            buf,
            section,
            inline,
            &resume_blocks,
            section_resumes,
            body_indent,
        );
    }
}
