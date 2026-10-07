# Test snapshots

`helm_text.txt` and `helm_json.txt` capture dump and JSON output for the committed UE 4.27 Helm fixture. Summary output for all four committed assets lives in `tests/baseline-snapshots/`.

After an intentional output change, regenerate and review the snapshots

```sh
UPDATE_SNAPSHOTS=1 cargo test --locked
git diff -- tests/snapshots/ tests/baseline-snapshots/
```

To update only dump and JSON snapshots, add `--test integration`. To update only summaries, add `--test v2_baseline`.
