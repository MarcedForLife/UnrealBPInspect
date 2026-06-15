//! JSON emitter for the decoded statement tree.
//!
//! Serialises `DecodedAsset` to pretty-printed JSON using the serde derives
//! on all IR types (`serde_json::to_string_pretty`).

use crate::bytecode::asset::DecodedAsset;

/// Emit the decoded Blueprint (Unreal Blueprint) asset as pretty-printed JSON.
///
/// Returns a JSON string. On serialisation failure (which should not occur for
/// well-formed IR types), falls back to an empty object `{}`.
pub fn emit_json(asset: &DecodedAsset) -> String {
    serde_json::to_string_pretty(asset).unwrap_or_else(|_| "{}".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::asset::{DecodedAsset, Event, Function};
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::Stmt;

    fn empty_asset() -> DecodedAsset {
        DecodedAsset {
            functions: vec![],
            events: vec![],
            resume_bodies: std::collections::BTreeMap::new(),
        }
    }

    #[test]
    fn empty_asset_serializes_to_valid_json() {
        let output = emit_json(&empty_asset());
        let parsed: serde_json::Value =
            serde_json::from_str(&output).expect("output must be valid JSON");
        assert!(
            parsed.get("functions").is_some(),
            "must have 'functions' key"
        );
        assert!(parsed.get("events").is_some(), "must have 'events' key");
        assert_eq!(parsed["functions"].as_array().unwrap().len(), 0);
        assert_eq!(parsed["events"].as_array().unwrap().len(), 0);
    }

    #[test]
    fn function_with_call_serializes_with_expected_keys() {
        let asset = DecodedAsset {
            functions: vec![Function {
                name: "MyFunc".into(),
                export_index: None,
                body: vec![Stmt::Call {
                    func: Expr::Var("DoThing".into()),
                    args: vec![Expr::Literal("42".into())],
                    offset: 0x0010,
                }],
            }],
            events: vec![],
            resume_bodies: std::collections::BTreeMap::new(),
        };
        let output = emit_json(&asset);
        let parsed: serde_json::Value =
            serde_json::from_str(&output).expect("output must be valid JSON");

        let functions = parsed["functions"].as_array().unwrap();
        assert_eq!(functions.len(), 1);
        assert_eq!(functions[0]["name"], "MyFunc");
        assert!(functions[0]["body"].is_array());
    }

    #[test]
    fn roundtrip_via_serde_value() {
        let asset = DecodedAsset {
            functions: vec![Function {
                name: "RoundtripFunc".into(),
                export_index: None,
                body: vec![Stmt::Return {
                    value: Some(Expr::Literal("true".into())),
                    offset: 0x0000,
                }],
            }],
            events: vec![Event {
                name: "OnBeginPlay".into(),
                export_index: None,
                body: vec![],
            }],
            resume_bodies: std::collections::BTreeMap::new(),
        };

        let json_str = emit_json(&asset);
        // Deserialise back into a typed asset to verify structural round-trip.
        let restored: DecodedAsset =
            serde_json::from_str(&json_str).expect("round-trip deserialisation must succeed");

        assert_eq!(restored.functions.len(), 1);
        assert_eq!(restored.functions[0].name, "RoundtripFunc");
        assert_eq!(restored.events.len(), 1);
        assert_eq!(restored.events[0].name, "OnBeginPlay");
    }

    #[test]
    fn output_is_pretty_printed() {
        let asset = empty_asset();
        let output = emit_json(&asset);
        // Pretty-printed JSON contains newlines and indentation spaces.
        assert!(
            output.contains('\n'),
            "output must contain newlines for pretty-print"
        );
    }
}
