//! Top-down recursive-descent parser over the decoder's output forms.
//!
//! `parse_expr` is the public entry. It tokenizes, then drives a
//! precedence-climbing parser. Any unrecognized shape is returned as
//! `Expr::Unknown(input)` and the parser never panics.
//!
//! `parse_stmt` sits on top and recognises the decoder's statement
//! forms (flow opcodes, returns, assignments, bare calls). Unrecognised
//! shapes round-trip verbatim via `Stmt::Unknown(raw)`.

use super::types::{Expr, Stmt, SwitchArm};

/// Find a top-level `=` in `text` (one outside parens/brackets/braces and
/// outside string literals, not part of `==`/`<=`/`>=`/`!=`). Returns the
/// byte offset of the `=`, or `None` if no top-level assignment is present.
pub fn top_level_eq_split(text: &str) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut depth: i32 = 0;
    let mut in_single = false;
    let mut in_double = false;
    let mut prev: u8 = 0;
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if in_single {
            if c == b'\\' && i + 1 < bytes.len() {
                i += 2;
                prev = 0;
                continue;
            }
            if c == b'\'' {
                in_single = false;
            }
        } else if in_double {
            if c == b'\\' && i + 1 < bytes.len() {
                i += 2;
                prev = 0;
                continue;
            }
            if c == b'"' {
                in_double = false;
            }
        } else {
            match c {
                b'\'' => in_single = true,
                b'"' => in_double = true,
                b'(' | b'[' | b'{' => depth += 1,
                b')' | b']' | b'}' => depth -= 1,
                b'=' if depth == 0 => {
                    let next = bytes.get(i + 1).copied().unwrap_or(0);
                    if prev == b'=' || prev == b'<' || prev == b'>' || prev == b'!' {
                        // second char of a compound op
                    } else if next == b'=' {
                        i += 2;
                        prev = b'=';
                        continue;
                    } else {
                        return Some(i);
                    }
                }
                _ => {}
            }
        }
        prev = c;
        i += 1;
    }
    None
}

/// Find a top-level `+=` or `-=` in `text` (one outside
/// parens/brackets/braces and outside string literals). Returns the
/// byte offset of the operator plus which literal matched, or `None`
/// if no top-level compound assignment is present. Must not match
/// `==`, `!=`, `<=`, `>=`, nor a standalone `+` / `-`.
pub fn top_level_compound_assign_split(text: &str) -> Option<(usize, &'static str)> {
    let bytes = text.as_bytes();
    let mut depth: i32 = 0;
    let mut in_single = false;
    let mut in_double = false;
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if in_single {
            if c == b'\\' && i + 1 < bytes.len() {
                i += 2;
                continue;
            }
            if c == b'\'' {
                in_single = false;
            }
            i += 1;
            continue;
        }
        if in_double {
            if c == b'\\' && i + 1 < bytes.len() {
                i += 2;
                continue;
            }
            if c == b'"' {
                in_double = false;
            }
            i += 1;
            continue;
        }
        match c {
            b'\'' => in_single = true,
            b'"' => in_double = true,
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b'+' | b'-' if depth == 0 => {
                if bytes.get(i + 1).copied() == Some(b'=') && i > 0 {
                    let op: &'static str = if c == b'+' { "+=" } else { "-=" };
                    return Some((i, op));
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Parse a trimmed decoder-output expression into an `Expr` tree.
///
/// Input is expected to be the RHS of an assignment, a flow-opcode
/// body, a call-as-statement body, or similar, not a full statement
/// line. Any unrecognized shape is returned as `Expr::Unknown(input)`;
/// the parser never panics.
///
/// A trailing metadata annotation (`[persistent]` or
/// `/*resume:0xHEX*/`) is peeled off before parsing and re-attached as
/// an `Expr::Trailer` wrapper so the inner shape stays parseable.
pub fn parse_expr(input: &str) -> Expr {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Expr::Unknown(input.to_owned());
    }
    if let Some((core, trailer)) = split_trailer(trimmed) {
        let inner = parse_expr_core(core);
        if !matches!(inner, Expr::Unknown(_)) {
            return Expr::Trailer {
                inner: Box::new(inner),
                trailer: trailer.to_owned(),
            };
        }
        return Expr::Unknown(input.to_owned());
    }
    parse_expr_core(trimmed)
}

/// Core `Expr` parser without trailer handling. Separated so
/// `parse_expr` can peel a trailing metadata annotation first and
/// recurse cleanly on the inner shape.
fn parse_expr_core(input: &str) -> Expr {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Expr::Unknown(input.to_owned());
    }
    if let Some(tail) = trimmed.strip_prefix("out ") {
        let inner = parse_expr_core(tail);
        if !matches!(inner, Expr::Unknown(_)) {
            return Expr::Out(Box::new(inner));
        }
        return Expr::Unknown(input.to_owned());
    }
    let tokens = match tokenize(trimmed) {
        Some(tokens) => tokens,
        None => return Expr::Unknown(input.to_owned()),
    };
    if tokens.is_empty() {
        return Expr::Unknown(input.to_owned());
    }
    let mut parser = Parser { tokens, pos: 0 };
    let expr = parser.parse_ternary();
    if !parser.at_end() || contains_unknown(&expr) {
        return Expr::Unknown(input.to_owned());
    }
    expr
}

/// Peel a recognised trailing metadata annotation off `text`, if any.
///
/// Returns `(core, trailer)` where `trailer` still contains the
/// leading separator (space before `[` or `/*`), so a literal
/// `{core}{trailer}` reassembly reproduces `text` byte-for-byte.
///
/// Recognised shapes:
/// - ` [persistent]` (from `EX_LET_VALUE_ON_PERSISTENT_FRAME` in
///   `decode/match_op.rs`)
/// - ` /*resume:0xHEX*/` (from `format_call_or_operator` in
///   `bytecode/format.rs`, appended to latent calls like `Delay`)
pub(super) fn split_trailer(text: &str) -> Option<(&str, &str)> {
    const PERSISTENT: &str = " [persistent]";
    if let Some(core) = text.strip_suffix(PERSISTENT) {
        let trailer_start = core.len();
        return Some((core, &text[trailer_start..]));
    }
    // Match ` /*resume:0xHEX*/` where HEX is one or more hex digits.
    const RESUME_END: &str = "*/";
    const RESUME_PREFIX: &str = " /*resume:0x";
    if let Some(stripped) = text.strip_suffix(RESUME_END) {
        if let Some(prefix_pos) = stripped.rfind(RESUME_PREFIX) {
            let hex_start = prefix_pos + RESUME_PREFIX.len();
            let hex = &stripped[hex_start..];
            if !hex.is_empty() && hex.chars().all(|c| c.is_ascii_hexdigit()) {
                let core = &text[..prefix_pos];
                let trailer = &text[prefix_pos..];
                return Some((core, trailer));
            }
        }
    }
    None
}

/// A subtree carries a failure marker (`Unknown(String::new())`) when a
/// child parser couldn't progress. The top-level `parse_expr` collapses
/// that into a single `Unknown(input)` so callers see one consistent
/// fallback shape.
fn contains_unknown(expr: &Expr) -> bool {
    match expr {
        Expr::Unknown(_) => true,
        Expr::Call { args, .. } => args.iter().any(contains_unknown),
        Expr::MethodCall { recv, args, .. } => {
            contains_unknown(recv) || args.iter().any(contains_unknown)
        }
        Expr::FieldAccess { recv, .. } => contains_unknown(recv),
        Expr::Index { recv, idx } => contains_unknown(recv) || contains_unknown(idx),
        Expr::Binary { lhs, rhs, .. } => contains_unknown(lhs) || contains_unknown(rhs),
        Expr::Unary { operand, .. } => contains_unknown(operand),
        Expr::Cast { inner, .. } => contains_unknown(inner),
        Expr::StructConstruct { fields, .. } => {
            fields.iter().any(|(_, value)| contains_unknown(value))
        }
        Expr::Select {
            cond,
            then_expr,
            else_expr,
        }
        | Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => contains_unknown(cond) || contains_unknown(then_expr) || contains_unknown(else_expr),
        Expr::Switch {
            scrut,
            arms,
            default,
        } => {
            contains_unknown(scrut)
                || arms
                    .iter()
                    .any(|arm| contains_unknown(&arm.pat) || contains_unknown(&arm.body))
                || default.as_deref().is_some_and(contains_unknown)
        }
        Expr::Trailer { inner, .. } => contains_unknown(inner),
        Expr::Out(inner) => contains_unknown(inner),
        Expr::ArrayLit(items) => items.iter().any(contains_unknown),
        Expr::Literal(_) | Expr::Var(_) => false,
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    /// Identifier or dotted-identifier fragment (`Foo`, `self`, `$Tmp_1`).
    Ident(String),
    /// Decimal or hex integer / float literal, including trailing `L`/`UL`.
    Num(String),
    /// Double-quoted string literal, stored with the surrounding quotes.
    Str(String),
    /// Single-quoted name literal, stored with the surrounding quotes.
    Name(String),
    /// Punctuation or multi-char operator, stored as-is (e.g. `==`, `&&`, `<=`).
    Punct(&'static str),
}

/// Split the input into tokens. Returns `None` on bad quoting so the
/// caller can fall back to `Expr::Unknown`.
fn tokenize(input: &str) -> Option<Vec<Tok>> {
    let bytes = input.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if b == b'"' {
            let start = i;
            i += 1;
            while i < bytes.len() && bytes[i] != b'"' {
                if bytes[i] == b'\\' && i + 1 < bytes.len() {
                    i += 2;
                } else {
                    i += 1;
                }
            }
            if i >= bytes.len() {
                return None;
            }
            i += 1;
            tokens.push(Tok::Str(input[start..i].to_owned()));
            continue;
        }
        if b == b'\'' {
            let start = i;
            i += 1;
            while i < bytes.len() && bytes[i] != b'\'' {
                i += 1;
            }
            if i >= bytes.len() {
                return None;
            }
            i += 1;
            tokens.push(Tok::Name(input[start..i].to_owned()));
            continue;
        }
        if b.is_ascii_digit() || (b == b'.' && peek_digit(bytes, i + 1)) {
            let start = i;
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'.' || bytes[i] == b'_')
            {
                i += 1;
            }
            tokens.push(Tok::Num(input[start..i].to_owned()));
            continue;
        }
        if b == b'-' && is_numeric_start(bytes, i + 1) && prev_allows_unary(&tokens) {
            let start = i;
            i += 1;
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'.' || bytes[i] == b'_')
            {
                i += 1;
            }
            tokens.push(Tok::Num(input[start..i].to_owned()));
            continue;
        }
        if is_ident_start(b) {
            let start = i;
            while i < bytes.len() && is_ident_cont(bytes[i]) {
                i += 1;
            }
            let ident = &input[start..i];
            // Blueprint FNames can contain spaces (e.g. `Evaluate
            // Movement Sounds`, `Day Length`). Merge space-delimited
            // capitalized words into a single ident, but only when the
            // surrounding context expects a name. See
            // `can_merge_spaced_ident` and
            // `is_name_expected_position` for the guardrails.
            let first_is_capitalized = ident
                .as_bytes()
                .first()
                .is_some_and(|b| b.is_ascii_uppercase());
            if first_is_capitalized
                && !is_protected_keyword(ident)
                && is_name_expected_position(&tokens)
            {
                let merge_end = scan_spaced_ident_suffix(bytes, i);
                if merge_end > i {
                    tokens.push(Tok::Ident(input[start..merge_end].to_owned()));
                    i = merge_end;
                    continue;
                }
            }
            tokens.push(Tok::Ident(ident.to_owned()));
            continue;
        }
        // Multi-char punctuation (order matters, longest first).
        let remaining = &input[i..];
        let punct = match_punct(remaining);
        if let Some(p) = punct {
            tokens.push(Tok::Punct(p));
            i += p.len();
            continue;
        }
        return None;
    }
    Some(tokens)
}

fn peek_digit(bytes: &[u8], at: usize) -> bool {
    bytes.get(at).is_some_and(|b| b.is_ascii_digit())
}

fn is_numeric_start(bytes: &[u8], at: usize) -> bool {
    match bytes.get(at) {
        Some(b) if b.is_ascii_digit() => true,
        Some(b'.') => peek_digit(bytes, at + 1),
        _ => false,
    }
}

fn prev_allows_unary(tokens: &[Tok]) -> bool {
    match tokens.last() {
        None => true,
        Some(Tok::Punct(p)) => !matches!(*p, ")" | "]" | "}"),
        _ => false,
    }
}

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_' || b == b'$'
}

fn is_ident_cont(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'$'
}

/// Reserved words that must never be swallowed into a space-merged
/// identifier. Covers statement-start keywords (`if`, `for`, ...),
/// expression-start keywords handled elsewhere (`out`, `switch`, ...),
/// and common value keywords (`true`, `false`, `null`, ...). Checked
/// against the first bareword read; if it matches, the spaced-ident
/// merge is not attempted.
fn is_protected_keyword(ident: &str) -> bool {
    matches!(
        ident,
        "if" | "for"
            | "while"
            | "else"
            | "return"
            | "jump"
            | "push_flow"
            | "pop_flow"
            | "pop_flow_if_not"
            | "continue_if_not"
            | "jump_computed"
            | "out"
            | "self"
            | "true"
            | "false"
            | "null"
            | "None"
            | "new"
            | "weak"
            | "match"
            | "break"
            | "continue"
            | "let"
            | "in"
            | "to"
            | "switch"
            | "nop"
    )
}

/// True when the next token emitted starts a name. The first-word
/// capitalization check plus the keyword protection list stop
/// `a + b` / `a Plus b` / `if cond` patterns from being merged even
/// when this returns true, so we only need to rule out positions
/// where an ident cannot legally appear (after `)` / `]` / `}` etc.,
/// which would be a syntax error anyway).
fn is_name_expected_position(tokens: &[Tok]) -> bool {
    match tokens.last() {
        None => true,
        Some(Tok::Punct(p)) => !matches!(*p, ")" | "]" | "}"),
        _ => false,
    }
}

/// Scan forward from `pos` in `bytes`, consuming ` `+`[A-Z][A-Za-z0-9_]*`
/// repeatedly. Returns the new cursor position (`== pos` means no
/// merge fired). The capitalized-bareword follow-up rule is the key
/// safety gate: it means `if cond` never merges (because `cond` starts
/// lowercase), while `Evaluate Movement Sounds` does.
fn scan_spaced_ident_suffix(bytes: &[u8], pos: usize) -> usize {
    let mut end = pos;
    loop {
        // Exactly one space between words. Multi-space sequences would
        // be suspicious and the decoder never emits them inside names.
        if bytes.get(end).copied() != Some(b' ') {
            return end;
        }
        let next_start = end + 1;
        let Some(first) = bytes.get(next_start).copied() else {
            return end;
        };
        if !first.is_ascii_uppercase() {
            return end;
        }
        let mut scan = next_start + 1;
        while scan < bytes.len() && is_ident_cont(bytes[scan]) {
            scan += 1;
        }
        end = scan;
    }
}

const PUNCTS: &[&str] = &[
    "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+=", "-=", "(", ")", "[", "]", "{", "}", ",",
    ";", ":", "?", "+", "-", "*", "/", "%", "<", ">", "!", "&", "|", "^", "~", ".", "=",
];

fn match_punct(input: &str) -> Option<&'static str> {
    PUNCTS
        .iter()
        .find(|&candidate| input.starts_with(candidate))
        .copied()
}

struct Parser {
    tokens: Vec<Tok>,
    pos: usize,
}

impl Parser {
    fn at_end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn peek(&self) -> Option<&Tok> {
        self.tokens.get(self.pos)
    }

    fn bump(&mut self) -> Option<Tok> {
        let tok = self.tokens.get(self.pos).cloned();
        if tok.is_some() {
            self.pos += 1;
        }
        tok
    }

    fn eat_punct(&mut self, p: &str) -> bool {
        if matches!(self.peek(), Some(Tok::Punct(q)) if *q == p) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn parse_ternary(&mut self) -> Expr {
        let cond = self.parse_or();
        if self.eat_punct("?") {
            let then_expr = self.parse_ternary();
            if !self.eat_punct(":") {
                return Expr::Unknown(String::new());
            }
            let else_expr = self.parse_ternary();
            return Expr::Ternary {
                cond: Box::new(cond),
                then_expr: Box::new(then_expr),
                else_expr: Box::new(else_expr),
            };
        }
        cond
    }

    fn parse_or(&mut self) -> Expr {
        self.parse_left_assoc(&["||"], Self::parse_and)
    }

    fn parse_and(&mut self) -> Expr {
        self.parse_left_assoc(&["&&"], Self::parse_bitor)
    }

    fn parse_bitor(&mut self) -> Expr {
        self.parse_left_assoc(&["|"], Self::parse_bitxor)
    }

    fn parse_bitxor(&mut self) -> Expr {
        self.parse_left_assoc(&["^"], Self::parse_bitand)
    }

    fn parse_bitand(&mut self) -> Expr {
        self.parse_left_assoc(&["&"], Self::parse_equality)
    }

    fn parse_equality(&mut self) -> Expr {
        self.parse_left_assoc(&["==", "!="], Self::parse_relational)
    }

    fn parse_relational(&mut self) -> Expr {
        self.parse_left_assoc(&["<=", ">=", "<", ">"], Self::parse_shift)
    }

    fn parse_shift(&mut self) -> Expr {
        self.parse_left_assoc(&["<<", ">>"], Self::parse_additive)
    }

    fn parse_additive(&mut self) -> Expr {
        self.parse_left_assoc(&["+", "-"], Self::parse_multiplicative)
    }

    fn parse_multiplicative(&mut self) -> Expr {
        self.parse_left_assoc(&["*", "/", "%"], Self::parse_unary)
    }

    fn parse_left_assoc(
        &mut self,
        ops: &[&'static str],
        mut next: impl FnMut(&mut Self) -> Expr,
    ) -> Expr {
        let mut lhs = next(self);
        loop {
            let matched = match self.peek() {
                Some(Tok::Punct(p)) => ops.iter().find(|op| **op == *p).copied(),
                _ => None,
            };
            let Some(op) = matched else { break };
            self.pos += 1;
            let rhs = next(self);
            lhs = Expr::Binary {
                op: op.to_owned(),
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }
        lhs
    }

    fn parse_unary(&mut self) -> Expr {
        match self.peek() {
            Some(Tok::Punct(p)) if matches!(*p, "!" | "-" | "~") => {
                let op = *p;
                self.pos += 1;
                let operand = self.parse_unary();
                Expr::Unary {
                    op: op.to_owned(),
                    operand: Box::new(operand),
                }
            }
            _ => self.parse_postfix(),
        }
    }

    fn parse_postfix(&mut self) -> Expr {
        let mut expr = self.parse_primary();
        loop {
            match self.peek() {
                Some(Tok::Punct(".")) => {
                    self.pos += 1;
                    let Some(Tok::Ident(name)) = self.bump() else {
                        return Expr::Unknown(String::new());
                    };
                    if matches!(self.peek(), Some(Tok::Punct("("))) {
                        self.pos += 1;
                        let Some(args) = self.parse_call_args() else {
                            return Expr::Unknown(String::new());
                        };
                        expr = Expr::MethodCall {
                            recv: Box::new(expr),
                            name,
                            args,
                        };
                    } else {
                        expr = Expr::FieldAccess {
                            recv: Box::new(expr),
                            field: name,
                        };
                    }
                }
                Some(Tok::Punct("[")) => {
                    self.pos += 1;
                    let idx = self.parse_ternary();
                    if !self.eat_punct("]") {
                        return Expr::Unknown(String::new());
                    }
                    expr = Expr::Index {
                        recv: Box::new(expr),
                        idx: Box::new(idx),
                    };
                }
                _ => break,
            }
        }
        expr
    }

    fn parse_primary(&mut self) -> Expr {
        let Some(tok) = self.bump() else {
            return Expr::Unknown(String::new());
        };
        match tok {
            Tok::Num(n) => Expr::Literal(n),
            Tok::Str(s) => Expr::Literal(s),
            Tok::Name(n) => Expr::Literal(n),
            Tok::Punct("(") => {
                let inner = self.parse_ternary();
                if !self.eat_punct(")") {
                    return Expr::Unknown(String::new());
                }
                inner
            }
            Tok::Punct("[") => self.parse_array_lit(),
            Tok::Ident(name) => self.parse_ident_tail(name),
            _ => Expr::Unknown(String::new()),
        }
    }

    /// Parse a bracketed array literal `[e1, e2, ...]`. The opening
    /// `[` has already been consumed. Empty `[]` is valid.
    fn parse_array_lit(&mut self) -> Expr {
        let mut items = Vec::new();
        if self.eat_punct("]") {
            return Expr::ArrayLit(items);
        }
        loop {
            let item = self.parse_ternary();
            items.push(item);
            if self.eat_punct(",") {
                continue;
            }
            if self.eat_punct("]") {
                return Expr::ArrayLit(items);
            }
            return Expr::Unknown(String::new());
        }
    }

    /// After consuming an identifier, decide whether it's a bare var,
    /// a free call, a cast, or a switch. Dotted forms like
    /// `obj.Field.Method(arg)` are handled by `parse_postfix`, which
    /// turns each `.` into a `FieldAccess` or `MethodCall`.
    fn parse_ident_tail(&mut self, name: String) -> Expr {
        if name == "switch" && matches!(self.peek(), Some(Tok::Punct("("))) {
            return self.parse_switch();
        }
        if matches!(self.peek(), Some(Tok::Punct("<"))) && looks_like_cast(&self.tokens, self.pos) {
            return self.parse_cast(name);
        }
        if matches!(self.peek(), Some(Tok::Punct("("))) {
            self.pos += 1;
            let Some(args) = self.parse_call_args() else {
                return Expr::Unknown(String::new());
            };
            return Expr::Call { name, args };
        }
        Expr::Var(name)
    }

    /// Returns `None` when the argument list is malformed (missing `)`
    /// or bad separator) so callers propagate an `Unknown` outward.
    fn parse_call_args(&mut self) -> Option<Vec<Expr>> {
        let mut args = Vec::new();
        if self.eat_punct(")") {
            return Some(args);
        }
        loop {
            let arg = self.parse_ternary();
            args.push(arg);
            if self.eat_punct(",") {
                continue;
            }
            if self.eat_punct(")") {
                return Some(args);
            }
            return None;
        }
    }

    fn parse_cast(&mut self, kind: String) -> Expr {
        // Consume `<` ... `>` ( ... )
        if !self.eat_punct("<") {
            return Expr::Unknown(String::new());
        }
        let mut ty = String::new();
        let mut depth: i32 = 1;
        while let Some(tok) = self.peek().cloned() {
            if let Tok::Punct(">") = tok {
                depth -= 1;
                self.pos += 1;
                if depth == 0 {
                    break;
                }
                ty.push('>');
                continue;
            }
            if let Tok::Punct("<") = tok {
                depth += 1;
                ty.push('<');
                self.pos += 1;
                continue;
            }
            self.pos += 1;
            append_tok(&mut ty, &tok);
        }
        if depth != 0 {
            return Expr::Unknown(String::new());
        }
        if !self.eat_punct("(") {
            return Expr::Unknown(String::new());
        }
        let inner = self.parse_ternary();
        if !self.eat_punct(")") {
            return Expr::Unknown(String::new());
        }
        // Keep the cast-kind and type distinct. `Cast.ty` is the target
        // type text; the kind (`icast`, `cast_N`, ...) is preserved by
        // including both when the kind is not the default `icast`.
        let ty_text = if kind == "icast" {
            ty
        } else {
            format!("{}<{}>", kind, ty)
        };
        Expr::Cast {
            ty: ty_text,
            inner: Box::new(inner),
        }
    }

    fn parse_switch(&mut self) -> Expr {
        if !self.eat_punct("(") {
            return Expr::Unknown(String::new());
        }
        let scrut = self.parse_ternary();
        if !self.eat_punct(")") {
            return Expr::Unknown(String::new());
        }
        if !self.eat_punct("{") {
            return Expr::Unknown(String::new());
        }
        let mut arms = Vec::new();
        let mut default: Option<Box<Expr>> = None;
        if self.eat_punct("}") {
            return Expr::Switch {
                scrut: Box::new(scrut),
                arms,
                default,
            };
        }
        loop {
            // Default arm marker `_`.
            let is_default = matches!(self.peek(), Some(Tok::Ident(s)) if s == "_");
            if is_default {
                self.pos += 1;
                if !self.eat_punct(":") {
                    return Expr::Unknown(String::new());
                }
                let body = self.parse_ternary();
                default = Some(Box::new(body));
            } else {
                let pat = self.parse_ternary();
                if !self.eat_punct(":") {
                    return Expr::Unknown(String::new());
                }
                let body = self.parse_ternary();
                arms.push(SwitchArm { pat, body });
            }
            if self.eat_punct(",") {
                continue;
            }
            if self.eat_punct("}") {
                break;
            }
            return Expr::Unknown(String::new());
        }
        Expr::Switch {
            scrut: Box::new(scrut),
            arms,
            default,
        }
    }
}

/// True if the `<` at `pos` is the start of a cast `<Type>(...)` rather
/// than a relational operator. Walks balanced `<...>` and checks that
/// the token after the matching `>` is `(`.
fn looks_like_cast(tokens: &[Tok], pos: usize) -> bool {
    if !matches!(tokens.get(pos), Some(Tok::Punct("<"))) {
        return false;
    }
    let mut depth: i32 = 0;
    let mut scan = pos;
    while scan < tokens.len() {
        match tokens.get(scan) {
            Some(Tok::Punct("<")) => depth += 1,
            Some(Tok::Punct(">")) => {
                depth -= 1;
                if depth == 0 {
                    return matches!(tokens.get(scan + 1), Some(Tok::Punct("(")));
                }
            }
            Some(Tok::Punct("(" | ")" | "{" | "}" | "[" | "]" | ";" | "?")) => return false,
            None => return false,
            _ => {}
        }
        scan += 1;
    }
    false
}

fn append_tok(out: &mut String, tok: &Tok) {
    match tok {
        Tok::Ident(s) | Tok::Num(s) | Tok::Str(s) | Tok::Name(s) => out.push_str(s),
        Tok::Punct(p) => out.push_str(p),
    }
}

/// Parse a single post-structure line into a `Stmt`.
///
/// Recognises the flow-opcode forms (`pop_flow`, `pop_flow_if_not(...)`,
/// `push_flow 0xHEX`, `continue_if_not(...)`, `if !(...) jump 0xHEX`,
/// `jump 0xHEX`, `jump_computed(...)`, `return nop`, `return`), top-level
/// assignments, and bare calls. Anything else (comments, block
/// delimiters, `if` / `for` headers, labels, blank lines) is returned
/// as `Stmt::Unknown(input.to_owned())` verbatim for lossless round-trip.
///
/// A trailing metadata annotation (`[persistent]` or
/// `/*resume:0xHEX*/`) is peeled off before classification and
/// re-attached as a [`Stmt::WithTrailer`] wrapper so the inner shape
/// (an assignment or a bare call) can be recognised normally.
///
/// Never panics.
pub fn parse_stmt(input: &str) -> Stmt {
    let trimmed = input.trim();

    if let Some((core, trailer)) = split_trailer(trimmed) {
        let inner = parse_stmt_core(core);
        if !matches!(inner, Stmt::Unknown(_)) {
            return Stmt::WithTrailer {
                inner: Box::new(inner),
                trailer: trailer.to_owned(),
            };
        }
        return Stmt::Unknown(input.to_owned());
    }

    match parse_stmt_core(trimmed) {
        // Preserve original (untrimmed) input for the Unknown fallback
        // so comments, block delimiters, and labels round-trip
        // byte-for-byte through `fmt_stmt`.
        Stmt::Unknown(_) => Stmt::Unknown(input.to_owned()),
        other => other,
    }
}

/// Core `Stmt` parser without trailer handling. Separated so
/// `parse_stmt` can peel a trailing metadata annotation first and
/// recurse cleanly on the inner shape.
fn parse_stmt_core(input: &str) -> Stmt {
    let trimmed = input.trim();

    // Post-structure leaf markers. Precede the expression/flow dispatch so
    // a bare `}` / `break` / `//...` line classifies as its own variant
    // rather than slipping into `Stmt::Unknown`. Guarded by exact match
    // so `break 2` stays Unknown for later slices.
    //
    // `Stmt::Else` (`} else {`) is matched BEFORE `Stmt::BlockClose` so
    // the composite shape wins over a lone `}` prefix. Composite shapes
    // like `} else if (cond) {` aren't recognised by either matcher and
    // stay `Stmt::Unknown`.
    if trimmed == "} else {" {
        return Stmt::Else;
    }
    if trimmed == "}" {
        return Stmt::BlockClose;
    }
    if trimmed == "break" {
        return Stmt::Break;
    }
    if trimmed.starts_with("//") {
        return Stmt::Comment(trimmed.to_owned());
    }
    if let Some(rest) = trimmed.strip_prefix("if (") {
        if let Some(cond_text) = rest.strip_suffix(") {") {
            let cond = parse_expr(cond_text);
            if !contains_unknown(&cond) {
                return Stmt::IfOpen { cond };
            }
        }
    }

    if trimmed == "pop_flow" {
        return Stmt::PopFlow;
    }
    if trimmed == "return nop" {
        return Stmt::ReturnNop;
    }
    if trimmed == "return" {
        return Stmt::BareReturn;
    }

    if let Some(inner) = trimmed.strip_prefix("pop_flow_if_not(") {
        if let Some(body) = inner.strip_suffix(')') {
            let cond = parse_expr(body);
            if !matches!(cond, Expr::Unknown(_)) {
                return Stmt::PopFlowIfNot { cond };
            }
        }
    }

    if let Some(inner) = trimmed.strip_prefix("continue_if_not(") {
        if let Some(body) = inner.strip_suffix(')') {
            let cond = parse_expr(body);
            if !matches!(cond, Expr::Unknown(_)) {
                return Stmt::ContinueIfNot { cond };
            }
        }
    }

    if let Some(rest) = trimmed.strip_prefix("push_flow 0x") {
        if let Ok(target) = usize::from_str_radix(rest, 16) {
            return Stmt::PushFlow { target };
        }
    }

    if let Some(rest) = trimmed.strip_prefix("jump 0x") {
        if let Ok(target) = usize::from_str_radix(rest, 16) {
            return Stmt::Jump { target };
        }
    }

    if let Some(inner) = trimmed.strip_prefix("jump_computed(") {
        if let Some(body) = inner.strip_suffix(')') {
            let expr = parse_expr(body);
            if !matches!(expr, Expr::Unknown(_)) {
                return Stmt::JumpComputed { expr };
            }
        }
    }

    if let Some(rest) = trimmed.strip_prefix("if !(") {
        if let Some(jump_pos) = rest.rfind(") jump 0x") {
            let target_str = &rest[jump_pos + ") jump 0x".len()..];
            if let Ok(target) = usize::from_str_radix(target_str, 16) {
                let cond_text = &rest[..jump_pos];
                let cond = parse_expr(cond_text);
                if !matches!(cond, Expr::Unknown(_)) {
                    return Stmt::IfJump { cond, target };
                }
            }
        }
    }

    if let Some((pos, op)) = top_level_compound_assign_split(trimmed) {
        let lhs_text = trimmed[..pos].trim();
        let rhs_text = trimmed[pos + op.len()..].trim();
        let lhs = parse_expr(lhs_text);
        let rhs = parse_expr(rhs_text);
        if !matches!(lhs, Expr::Unknown(_)) && !matches!(rhs, Expr::Unknown(_)) {
            return Stmt::CompoundAssign {
                op: op.to_owned(),
                lhs,
                rhs,
            };
        }
    }

    if let Some(pos) = top_level_eq_split(trimmed) {
        let lhs_text = trimmed[..pos].trim();
        let rhs_text = trimmed[pos + 1..].trim();
        let lhs = parse_expr(lhs_text);
        let rhs = parse_expr(rhs_text);
        if !matches!(lhs, Expr::Unknown(_)) && !matches!(rhs, Expr::Unknown(_)) {
            return Stmt::Assignment { lhs, rhs };
        }
    }

    let expr = parse_expr(trimmed);
    if matches!(expr, Expr::Call { .. } | Expr::MethodCall { .. }) {
        return Stmt::Call { expr };
    }

    Stmt::Unknown(input.to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(s: &str) -> Expr {
        Expr::Literal(s.to_owned())
    }

    fn var(s: &str) -> Expr {
        Expr::Var(s.to_owned())
    }

    fn call(name: &str, args: Vec<Expr>) -> Expr {
        Expr::Call {
            name: name.to_owned(),
            args,
        }
    }

    fn binary(op: &str, lhs: Expr, rhs: Expr) -> Expr {
        Expr::Binary {
            op: op.to_owned(),
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    #[test]
    fn parses_integer_literal() {
        assert_eq!(parse_expr("42"), lit("42"));
    }

    #[test]
    fn parses_float_literal() {
        assert_eq!(parse_expr("3.14"), lit("3.14"));
    }

    #[test]
    fn parses_string_literal() {
        assert_eq!(parse_expr("\"hello\""), lit("\"hello\""));
    }

    #[test]
    fn parses_string_with_escape() {
        assert_eq!(parse_expr("\"a \\\" b\""), lit("\"a \\\" b\""));
    }

    #[test]
    fn parses_name_literal() {
        assert_eq!(parse_expr("'Foo'"), lit("'Foo'"));
    }

    #[test]
    fn parses_bare_identifier() {
        assert_eq!(parse_expr("Self"), var("Self"));
        assert_eq!(parse_expr("$Tmp_1"), var("$Tmp_1"));
    }

    #[test]
    fn parses_bool_like_identifier() {
        // `true` / `false` are just bare identifiers at this level.
        assert_eq!(parse_expr("true"), var("true"));
        assert_eq!(parse_expr("false"), var("false"));
    }

    #[test]
    fn unwraps_parens() {
        assert_eq!(parse_expr("(42)"), lit("42"));
        assert_eq!(parse_expr("((a))"), var("a"));
    }

    #[test]
    fn parses_free_call() {
        assert_eq!(
            parse_expr("GetThing(a, b)"),
            call("GetThing", vec![var("a"), var("b")])
        );
    }

    #[test]
    fn parses_nested_call() {
        assert_eq!(
            parse_expr("Add(Mul(a, b), c)"),
            call("Add", vec![call("Mul", vec![var("a"), var("b")]), var("c")])
        );
    }

    #[test]
    fn parses_field_access() {
        assert_eq!(
            parse_expr("self.VRMovementReference.MovementMode"),
            Expr::FieldAccess {
                recv: Box::new(Expr::FieldAccess {
                    recv: Box::new(var("self")),
                    field: "VRMovementReference".into(),
                }),
                field: "MovementMode".into(),
            }
        );
    }

    #[test]
    fn parses_method_chain() {
        assert_eq!(
            parse_expr("a.b.c()"),
            Expr::MethodCall {
                recv: Box::new(Expr::FieldAccess {
                    recv: Box::new(var("a")),
                    field: "b".into(),
                }),
                name: "c".into(),
                args: vec![],
            }
        );
    }

    #[test]
    fn parses_method_call_with_args() {
        assert_eq!(
            parse_expr("obj.Field.Method(arg)"),
            Expr::MethodCall {
                recv: Box::new(Expr::FieldAccess {
                    recv: Box::new(var("obj")),
                    field: "Field".into(),
                }),
                name: "Method".into(),
                args: vec![var("arg")],
            }
        );
    }

    #[test]
    fn parses_index_expr() {
        assert_eq!(
            parse_expr("arr[idx]"),
            Expr::Index {
                recv: Box::new(var("arr")),
                idx: Box::new(var("idx")),
            }
        );
    }

    #[test]
    fn parses_icast() {
        assert_eq!(
            parse_expr("icast<Interactable_BI_C>(GetThing())"),
            Expr::Cast {
                ty: "Interactable_BI_C".into(),
                inner: Box::new(call("GetThing", vec![])),
            }
        );
    }

    #[test]
    fn parses_binary_add() {
        assert_eq!(parse_expr("a + b"), binary("+", var("a"), var("b")));
    }

    #[test]
    fn parses_binary_logical() {
        assert_eq!(parse_expr("a && b"), binary("&&", var("a"), var("b")));
        assert_eq!(parse_expr("a || b"), binary("||", var("a"), var("b")));
    }

    #[test]
    fn parses_comparison_chain() {
        assert_eq!(parse_expr("a <= b"), binary("<=", var("a"), var("b")));
        assert_eq!(parse_expr("a == b"), binary("==", var("a"), var("b")));
    }

    #[test]
    fn precedence_mul_over_add() {
        // a + b * c -> a + (b * c)
        assert_eq!(
            parse_expr("a + b * c"),
            binary("+", var("a"), binary("*", var("b"), var("c"))),
        );
        // a * b + c -> (a * b) + c
        assert_eq!(
            parse_expr("a * b + c"),
            binary("+", binary("*", var("a"), var("b")), var("c")),
        );
    }

    #[test]
    fn left_associative_subtract() {
        // a - b - c -> (a - b) - c
        assert_eq!(
            parse_expr("a - b - c"),
            binary("-", binary("-", var("a"), var("b")), var("c")),
        );
    }

    #[test]
    fn parses_unary_not() {
        assert_eq!(
            parse_expr("!x"),
            Expr::Unary {
                op: "!".into(),
                operand: Box::new(var("x")),
            }
        );
    }

    #[test]
    fn parses_ternary() {
        assert_eq!(
            parse_expr("cond ? a : b"),
            Expr::Ternary {
                cond: Box::new(var("cond")),
                then_expr: Box::new(var("a")),
                else_expr: Box::new(var("b")),
            }
        );
    }

    #[test]
    fn parses_switch_with_default() {
        assert_eq!(
            parse_expr("switch(x) { 0: a, 1: b, _: c }"),
            Expr::Switch {
                scrut: Box::new(var("x")),
                arms: vec![
                    SwitchArm {
                        pat: lit("0"),
                        body: var("a"),
                    },
                    SwitchArm {
                        pat: lit("1"),
                        body: var("b"),
                    },
                ],
                default: Some(Box::new(var("c"))),
            }
        );
    }

    #[test]
    fn parses_switch_without_default() {
        // The decoder's actual output shape: no `_:` arm.
        assert_eq!(
            parse_expr("switch(idx) { 0: a, 1: b }"),
            Expr::Switch {
                scrut: Box::new(var("idx")),
                arms: vec![
                    SwitchArm {
                        pat: lit("0"),
                        body: var("a"),
                    },
                    SwitchArm {
                        pat: lit("1"),
                        body: var("b"),
                    },
                ],
                default: None,
            }
        );
    }

    #[test]
    fn parens_guard_precedence() {
        // (a + b) * c -> Binary(*, Binary(+, a, b), c)
        assert_eq!(
            parse_expr("(a + b) * c"),
            binary("*", binary("+", var("a"), var("b")), var("c")),
        );
    }

    #[test]
    fn dotted_call_becomes_method_chain() {
        // `Class.Func(arg)` is a MethodCall on the Class receiver.
        // (The decoder emits this shape for free library calls, and
        // printer passes render it back as `Class.Func(arg)`.)
        assert_eq!(
            parse_expr("KismetMathLibrary.VSize(v)"),
            Expr::MethodCall {
                recv: Box::new(var("KismetMathLibrary")),
                name: "VSize".into(),
                args: vec![var("v")],
            }
        );
    }

    #[test]
    fn compound_assign_split_matches_plus_equals() {
        let text = "x += y";
        let (pos, op) = top_level_compound_assign_split(text).unwrap();
        assert_eq!(op, "+=");
        assert_eq!(&text[pos..pos + 2], "+=");
    }

    #[test]
    fn compound_assign_split_matches_minus_equals() {
        let text = "x -= y";
        let (pos, op) = top_level_compound_assign_split(text).unwrap();
        assert_eq!(op, "-=");
        assert_eq!(&text[pos..pos + 2], "-=");
    }

    #[test]
    fn compound_assign_split_ignores_equality_and_relops() {
        assert!(top_level_compound_assign_split("x == y").is_none());
        assert!(top_level_compound_assign_split("x != y").is_none());
        assert!(top_level_compound_assign_split("x <= y").is_none());
        assert!(top_level_compound_assign_split("x >= y").is_none());
    }

    #[test]
    fn compound_assign_split_ignores_plain_add_sub() {
        assert!(top_level_compound_assign_split("x + y").is_none());
        assert!(top_level_compound_assign_split("x - y").is_none());
    }

    #[test]
    fn compound_assign_split_respects_depth() {
        assert!(top_level_compound_assign_split("[a += b]").is_none());
        assert!(top_level_compound_assign_split("f(a += b)").is_none());
        assert!(top_level_compound_assign_split("{a += b}").is_none());
    }

    #[test]
    fn compound_assign_split_ignores_leading_operator() {
        // Malformed `+= y` at pos 0 is ignored (not a corpus shape).
        assert!(top_level_compound_assign_split("+= y").is_none());
    }

    #[test]
    fn parses_spaced_ident_at_call_site() {
        assert_eq!(
            parse_expr("Evaluate Movement Sounds(0)"),
            call("Evaluate Movement Sounds", vec![lit("0")])
        );
    }

    #[test]
    fn parses_spaced_ident_after_dot() {
        assert_eq!(
            parse_expr("self.Foo.Day Length"),
            Expr::FieldAccess {
                recv: Box::new(Expr::FieldAccess {
                    recv: Box::new(var("self")),
                    field: "Foo".into(),
                }),
                field: "Day Length".into(),
            }
        );
    }

    #[test]
    fn parses_spaced_ident_in_binary_operands() {
        assert_eq!(
            parse_expr("Day Length + Night Length"),
            binary("+", var("Day Length"), var("Night Length")),
        );
    }

    #[test]
    fn parses_spaced_method_call_on_member() {
        assert_eq!(
            parse_expr("self.Weather.Select New Random Weather Type(true)"),
            Expr::MethodCall {
                recv: Box::new(Expr::FieldAccess {
                    recv: Box::new(var("self")),
                    field: "Weather".into(),
                }),
                name: "Select New Random Weather Type".into(),
                args: vec![var("true")],
            }
        );
    }

    #[test]
    fn spaced_ident_preserves_if_jump() {
        // The `if !(cond) jump 0x100` shape must keep working; `if`
        // and `jump` are keyword-protected so neither participates in
        // the space-merge and the statement stays IfJump.
        let stmt = parse_stmt("if !(cond) jump 0x100");
        assert_eq!(
            stmt,
            Stmt::IfJump {
                cond: var("cond"),
                target: 0x100,
            }
        );
    }

    #[test]
    fn spaced_ident_does_not_swallow_for_keyword() {
        // `for (...)` is not a recognized statement shape; must stay
        // Unknown, not become a merged `for (idx` ident.
        let input = "for (idx = 0 to 5) {";
        assert_eq!(parse_stmt(input), Stmt::Unknown(input.to_owned()));
    }

    #[test]
    fn spaced_ident_leaves_known_struct_calls_untouched() {
        // `Vec(...)` has no following space-capitalized word, so the
        // merge doesn't fire. Parses as a plain Call.
        assert_eq!(
            parse_expr("Vec(1.0, 2.0, 3.0)"),
            call("Vec", vec![lit("1.0"), lit("2.0"), lit("3.0")])
        );
    }

    #[test]
    fn spaced_ident_does_not_eat_out_keyword() {
        // `out` is Expr-prefix stripped before tokenization, and it's
        // keyword-protected so the merge never fires on the `out`
        // token itself.
        assert_eq!(parse_expr("out Hit"), Expr::Out(Box::new(var("Hit"))));
    }

    #[test]
    fn parses_block_close_marker() {
        assert_eq!(parse_stmt("}"), Stmt::BlockClose);
        assert_eq!(parse_stmt("  }  "), Stmt::BlockClose);
    }

    #[test]
    fn parses_break_marker() {
        assert_eq!(parse_stmt("break"), Stmt::Break);
        assert_eq!(parse_stmt("  break  "), Stmt::Break);
    }

    #[test]
    fn parses_comment_marker() {
        assert_eq!(
            parse_stmt("// a comment with spaces and $symbols"),
            Stmt::Comment("// a comment with spaces and $symbols".to_owned())
        );
    }

    #[test]
    fn parses_comment_marker_trims_leading_whitespace() {
        assert_eq!(
            parse_stmt("  // leading whitespace stripped"),
            Stmt::Comment("// leading whitespace stripped".to_owned())
        );
    }

    #[test]
    fn parses_empty_comment_marker() {
        // parse_stmt trims input on entry, so trailing whitespace is lost.
        assert_eq!(parse_stmt("// "), Stmt::Comment("//".to_owned()));
    }

    #[test]
    fn block_close_variant_guarded_by_exact_match() {
        // `} ` followed by non-else text (a label-ish shape) must not
        // be classified as BlockClose. The `Stmt::Else` matcher handles
        // `} else {` exclusively.
        let input = "} foo";
        assert_eq!(parse_stmt(input), Stmt::Unknown(input.to_owned()));
    }

    #[test]
    fn break_variant_guarded_by_exact_match() {
        // Multi-token shapes like `break 2` are not recognised, keep
        // the exact-match guard so they fall through to Unknown.
        let input = "break 2";
        assert_eq!(parse_stmt(input), Stmt::Unknown(input.to_owned()));
    }

    #[test]
    fn parses_if_open_simple_cond() {
        assert_eq!(
            parse_stmt("if (cond) {"),
            Stmt::IfOpen { cond: var("cond") }
        );
    }

    #[test]
    fn parses_if_open_compound_cond_and_whitespace() {
        assert_eq!(
            parse_stmt("  if ($x && $y) {  "),
            Stmt::IfOpen {
                cond: binary("&&", var("$x"), var("$y")),
            }
        );
    }

    #[test]
    fn parses_else_marker() {
        assert_eq!(parse_stmt("} else {"), Stmt::Else);
        assert_eq!(parse_stmt("  } else {  "), Stmt::Else);
    }

    #[test]
    fn else_if_composite_stays_unknown() {
        // `} else if (cond) {` is neither Else nor IfOpen, neither
        // matcher should claim it. A later slice can add a dedicated
        // variant if post-structure ever emits this shape.
        let input = "} else if (cond) {";
        assert_eq!(parse_stmt(input), Stmt::Unknown(input.to_owned()));
    }

    #[test]
    fn malformed_if_open_stays_unknown() {
        // Missing parens / wrong shape must fall through to Unknown.
        let input = "if ) {";
        assert_eq!(parse_stmt(input), Stmt::Unknown(input.to_owned()));
    }

    #[test]
    fn if_open_round_trips_through_fmt_stmt() {
        use super::super::print::fmt_stmt;
        let original = Stmt::IfOpen {
            cond: binary(
                "&&",
                binary("==", var("$a"), Expr::Literal("0".to_owned())),
                var("flag"),
            ),
        };
        let printed = fmt_stmt(&original);
        let reparsed = parse_stmt(&printed);
        assert_eq!(original, reparsed);
    }

    #[test]
    fn parse_expr_never_panics_on_garbage() {
        let cases = [
            "",
            "(",
            "((((((",
            "a b c",
            "\"",
            "switch(x) {",
            "icast<Foo(",
            "a + ",
            ")",
            "a ? b",
        ];
        for input in cases {
            let result = parse_expr(input);
            assert!(
                matches!(result, Expr::Unknown(_)),
                "expected Unknown for input {:?}, got {:?}",
                input,
                result
            );
        }
    }
}
