//! Ubergraph event-name and section resolution.

mod events;

pub(crate) use events::{clean_event_header, compute_action_key_events, display_event_name};
