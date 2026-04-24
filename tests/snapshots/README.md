# Test snapshots

Expected output captures used by the integration and round-trip tests
in `tests/`.

## Layout

- `helm_{summary,text,json}.txt` — snapshots for the committed
  `Helm_BP.uasset` fixtures (`samples/ue_*/Helm_BP.uasset`). Baseline
  regression coverage on `main`.
- `ir_roundtrip_divergences.txt`,
  `ir_stmt_byte_equality.txt`,
  `ir_unknown_fallback.txt`,
  `ir_stmt_unknown_fallback.txt` — harness snapshots for the typed
  expression / statement IR. The harness walks every `.uasset` under
  `samples/` and records parse-print divergences plus the `Unknown`
  fallback rate.

## Regenerating

After intentional output changes, regenerate the snapshots in one go:

```bash
UPDATE_SNAPSHOTS=1 cargo test
```

To regenerate a subset:

```bash
UPDATE_SNAPSHOTS=1 cargo test helm_summary_snapshot
UPDATE_SNAPSHOTS=1 cargo test --test bytecode_ir_roundtrip
```

Review the diff with `git diff tests/snapshots/` before committing and
make sure the changes match your expectation.
