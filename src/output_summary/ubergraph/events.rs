//! Event-name and section resolution for ubergraph sections.

use std::collections::{BTreeMap, HashMap};

/// Short action name from an InputAction stub, e.g.
/// `InpActEvt_Fly_K2Node_InputActionEvent_6` -> `Some("Fly")`.
pub(super) fn extract_input_action_name(section_name: &str) -> Option<&str> {
    let rest = section_name.strip_prefix("InpActEvt_")?;
    let end = rest.find("_K2Node_InputActionEvent_")?;
    Some(&rest[..end])
}

/// Trailing numeric suffix from an InputAction/InputAxis event name.
fn extract_event_suffix_number(section_name: &str) -> Option<u32> {
    let last_underscore = section_name.rfind('_')?;
    section_name[last_underscore + 1..].parse().ok()
}

/// Axis name from an InputAxis stub, e.g.
/// `InpAxisEvt_MouseX_K2Node_InputAxisEvent_0` -> `Some("MouseX")`.
fn extract_input_axis_name(section_name: &str) -> Option<&str> {
    let rest = section_name.strip_prefix("InpAxisEvt_")?;
    let end = rest.find("_K2Node_InputAxisEvent_")?;
    Some(&rest[..end])
}

/// Pressed/Released labels for InputAction events: for each action name,
/// lower suffix -> Pressed, higher -> Released; single event -> Pressed.
pub(crate) fn compute_action_key_events(section_names: &[&str]) -> HashMap<String, String> {
    // BTreeMap so the build below iterates actions in a deterministic order;
    // result keys are distinct event names so output is unaffected today.
    let mut by_action: BTreeMap<&str, Vec<(&str, u32)>> = BTreeMap::new();
    for &name in section_names {
        if let Some(action) = extract_input_action_name(name) {
            let num = extract_event_suffix_number(name).unwrap_or(0);
            by_action.entry(action).or_default().push((name, num));
        }
    }
    let mut result = HashMap::new();
    for (_, mut events) in by_action {
        events.sort_by_key(|&(_, num)| num);
        if events.len() == 1 {
            result.insert(events[0].0.to_string(), "Pressed".to_string());
        } else {
            result.insert(events[0].0.to_string(), "Pressed".to_string());
            for &(name, _) in &events[1..] {
                result.insert(name.to_string(), "Released".to_string());
            }
        }
    }
    result
}

/// Raw UberGraph section name -> bare display name (no signature):
/// - `InpActEvt_Jump_..._13` (Pressed) -> `InputAction_Jump_Pressed`
/// - `InpAxisEvt_MouseX_..._0` -> `InputAxis_MouseX`
/// - Other events (custom, regular) pass through.
///
/// Used by call graph and `// Called by:` trailers; see [`clean_event_header`]
/// for the signature-carrying variant.
pub(crate) fn display_event_name(
    raw_name: &str,
    action_key_events: &HashMap<String, String>,
) -> String {
    if let Some(action) = extract_input_action_name(raw_name) {
        let key_event = action_key_events
            .get(raw_name)
            .map(|s| s.as_str())
            .unwrap_or("Pressed");
        return format!("InputAction_{}_{}", action, key_event);
    }
    if let Some(axis) = extract_input_axis_name(raw_name) {
        return format!("InputAxis_{}", axis);
    }
    raw_name.to_string()
}

/// Raw UberGraph section name -> display name with signature. InputAxis
/// adds `(AxisValue: float)`; custom events pass through, caller appends `()`.
pub(crate) fn clean_event_header(
    raw_name: &str,
    action_key_events: &HashMap<String, String>,
) -> String {
    if extract_input_axis_name(raw_name).is_some() {
        let bare = display_event_name(raw_name, action_key_events);
        return format!("{}(AxisValue: float)", bare);
    }
    display_event_name(raw_name, action_key_events)
}
