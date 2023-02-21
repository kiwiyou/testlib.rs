use std::io::{self, Write};

/// Verdict values to return.
/// 
/// Each verdict corresponds to the unique exit code,
/// which is compatible with that of testlib.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(i32)]
pub enum Verdict {
    /// Accepted.
    Accepted = 0,
    /// Wrong Answer.
    Wrong = 1,
    /// Presentation Error.
    Presentation = 2,
    /// Failed.
    Fail = 3,
}

/// Halts current process and prints the verdict message.
///
/// The verdict string is prepended to the message.
pub fn quit(verdict: Verdict, message: impl AsRef<str>) -> ! {
    let message = message.as_ref().trim();
    let prepend = match verdict {
        Verdict::Accepted => "ok",
        Verdict::Wrong => "wrong answer",
        Verdict::Presentation => "wrong output format",
        Verdict::Fail => "FAIL",
    };
    writeln!(io::stderr(), "{prepend} {message}").unwrap();
    std::process::exit(verdict as i32)
}

/// Checks if the condition is true, otherwise quit with `Verdict::Wrong`.
pub fn ensure(cond: bool, message: impl AsRef<str>) {
    if !cond {
        quit(Verdict::Wrong, message);
    }
}

