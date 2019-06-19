use crate::Clause;
use super::Teacher;

/// A simple teacher that explores automata runs to check guesses.
pub struct Explorer {
    // ...
}

impl Explorer {
    pub fn new() -> Explorer {
        Explorer {
            // ...
        }
    }
}

impl Teacher for Explorer {
    fn assert(&self, clause: Clause) {
        // ...
    }
}
