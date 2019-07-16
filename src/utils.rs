use std::fmt;

pub struct PList<'a, T: fmt::Display>(pub &'a [T], pub &'a str);

impl<'a, T: fmt::Display> fmt::Display for PList<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0.split_first() {
            Some((head, tail)) => {
                head.fmt(f)?;
                for e in tail.iter() {
                    write!(f, "{}", self.1)?;
                    e.fmt(f)?;
                }
                Ok(())
            },
            None => Ok(())
        }
    }
}
