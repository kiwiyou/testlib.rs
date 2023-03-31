use std::{
    borrow::Borrow,
    collections::hash_map::DefaultHasher,
    f32::consts::E,
    fmt::Debug,
    hash::{Hash, Hasher},
    io::Read,
    ops::{Bound, RangeBounds},
    str::FromStr,
};

#[repr(i32)]
pub enum Verdict {
    Ok = 0,
    Wrong = 1,
    Presentation = 2,
    Fail = 3,
}

impl Verdict {
    pub fn name(&self) -> &'static str {
        match self {
            Self::Ok => "ok",
            Self::Wrong => "wrong answer",
            Self::Presentation => "wrong output format",
            Self::Fail => "FAIL",
        }
    }
}

#[macro_export]
macro_rules! quit {
    ($verdict:ident, $($t:tt)*) => {{
        use std::io::*;
        let mut lock = std::io::stderr().lock();
        lock.write_fmt(format_args!("{} ", self::Verdict::$verdict.name())).ok();
        lock.write_fmt(format_args!($($t)*)).ok();
        lock.write(self::EOLN.as_bytes()).ok();
        std::process::exit(self::Verdict::$verdict as i32);
    }};
}

const BUF: usize = 1 << 17;
/// Validator for [`std::io::Read`].
pub struct Validator<R> {
    buf: Vec<u8>,
    front: usize,
    reader: R,
    line: usize,
}

impl<R: Read> Validator<R> {
    /// Creates a new validator wrapping `reader`.
    pub fn new(reader: R) -> Self {
        Self {
            buf: vec![0; BUF],
            front: BUF,
            reader,
            line: 1,
        }
    }
    /// Reads a byte without advancing cursor.
    fn read_byte(&mut self) -> Option<u8> {
        let ret = if self.front < self.buf.len() {
            self.buf[self.front]
        } else {
            let capacity = self.buf.capacity();
            self.buf.resize(capacity, 0);
            let len = self
                .reader
                .read(&mut self.buf)
                .expect("cannot read from reader");
            if len == 0 {
                return None;
            }
            self.buf.truncate(len);
            self.front = 0;
            self.buf[self.front]
        };
        Some(ret)
    }
    /// Reads an integer (signed/unsigned) with bound check, panics if not found or out of bound.
    pub fn read_int<
        Int: FromStr + PartialOrd,
        Range: Borrow<Bounds>,
        Bounds: RangeBounds<Int> + Debug,
    >(
        &mut self,
        range: Range,
        name: &str,
    ) -> Int {
        let range = range.borrow();
        let mut s = vec![];
        loop {
            let digit = self.read_byte();
            match digit {
                Some(digit @ b'-' | digit @ b'0'..=b'9') => {
                    s.push(digit);
                    self.front += 1;
                }
                _ => break,
            }
        }
        if s.is_empty() {
            quit!(
                Fail,
                "Expected integer {name}, found EOF (line {})",
                self.line
            );
        }
        // Safety guarantee: s only contains b'-' and b'0'..=b'9'.
        let s = unsafe { String::from_utf8_unchecked(s) };
        match s.parse() {
            Ok(v) if range.contains(&v) => v,
            _ => quit!(
                Fail,
                "Expected integer {name} in bound {range:?}, found {s:?} (line {})",
                self.line
            ),
        }
    }
    /// Read integers separated by space, panics if not found or out of range.
    pub fn read_ints<
        Int: FromStr + PartialOrd,
        Range: Borrow<Bounds>,
        Bounds: RangeBounds<Int> + Debug,
    >(
        &mut self,
        n: usize,
        range: Range,
        name: &str,
    ) -> Vec<Int> {
        let range = range.borrow();
        let mut out = Vec::with_capacity(n);
        for i in 1..=n {
            let v = self.read_int::<Int, &Bounds, Bounds>(&range, &format!("{name}[{i}]"));
            out.push(v);
            if i != n {
                self.read_space();
            }
        }
        out
    }
    /// Reads a space, panics if not found.
    pub fn read_space(&mut self) {
        let ch = self.read_byte();
        if ch != Some(b' ') {
            quit!(
                Fail,
                "Expected space, found {:?} (line {})",
                ch.map(|b| b as char),
                self.line,
            );
        }
        self.front += 1;
    }
    /// Reads a token, panics if not found or invalid utf-8.
    pub fn read_token(&mut self, name: &str) -> String {
        let mut s = vec![];
        while let Some(ch) = self.read_byte() {
            if ch.is_ascii_whitespace() {
                break;
            }
            s.push(ch);
        }
        if s.is_empty() {
            quit!(
                Fail,
                "Expected string {name}, found EOF (line {})",
                self.line
            );
        }
        match String::from_utf8(s) {
            Ok(s) => s,
            Err(_) => quit!(
                Fail,
                "Expected utf-8 string {name}, found invalid byte sequence (line {})",
                self.line
            ),
        }
    }
    /// Reads a line, panics if not found or invalid utf-8.
    pub fn read_line(&mut self, name: &str) -> String {
        let mut s = vec![];
        while let Some(ch) = self.read_byte() {
            if ch == b'\r' || ch == b'\n' {
                break;
            }
            s.push(ch);
        }
        if s.is_empty() {
            quit!(
                Fail,
                "Expected string {name}, found EOF (line {})",
                self.line
            );
        }
        match String::from_utf8(s) {
            Ok(s) => s,
            Err(_) => quit!(
                Fail,
                "Expected utf-8 string {name}, found invalid byte sequence (line {})",
                self.line
            ),
        }
    }
    /// Checks for newline `"\n"` ad `"\r\n"`, panics if not found.
    pub fn read_eoln(&mut self) {
        match self.read_byte() {
            Some(b'\r') => {
                self.front += 1;
                if let Some(b'\n') = self.read_byte() {
                    self.front += 1;
                    self.line += 1;
                } else {
                    quit!(Fail, "Expected EOLN, found '\\r' (line {})", self.line);
                }
            }
            Some(b'\n') => {
                self.front += 1;
                self.line += 1;
            }
            None => {
                quit!(Fail, "Expected EOLN, found EOF (line {})", self.line);
            }
            Some(other) => {
                quit!(
                    Fail,
                    "Expected EOLN, found {:?} (line {})",
                    other as char,
                    self.line
                );
            }
        }
    }
    /// Checks for EOF, panics if not found.
    pub fn read_eof(&mut self) {
        if let Some(ch) = self.read_byte() {
            quit!(
                Fail,
                "Expected EOF, found {:?} (line {})",
                ch as char,
                self.line
            );
        }
    }
    /// Skip whitespaces and check if it reached EOF.
    pub fn seek_eof(&mut self) -> bool {
        loop {
            match self.read_byte() {
                Some(b'\n') => {
                    self.front += 1;
                    self.line += 1;
                }
                Some(ch) if ch.is_ascii_whitespace() => self.front += 1,
                Some(_) => break false,
                None => break true,
            }
        }
    }
}

#[cfg(windows)]
pub const EOLN: &str = "\r\n";
#[cfg(not(windows))]
pub const EOLN: &str = "\n";

/// Returns process argument with index, parsed as `T`.
pub fn opt<T: FromStr<Err = E>, E: Debug>(index: usize) -> Option<T> {
    let s = std::env::args().nth(index)?;
    Some(s.parse().expect("Cannot parse argument"))
}

/// Returns process argument with name, parsed as `T`.
///
/// if arguments contain `-name value`, `opt_with_name(name)` returns `value`.
pub fn opt_with_name<T: FromStr<Err = E>, E: Debug>(name: &str) -> Option<T> {
    let mut args = std::env::args();
    args.find(|arg| arg.strip_prefix("-") == Some(name))?;
    let arg = args.next()?;
    Some(arg.parse().expect("Cannot parse argument"))
}

/// Pseudo random number generator seeded by process arguments.
pub struct Rng([u64; 4]);

impl Rng {
    fn split_mix(v: u64) -> u64 {
        let mut z = v.wrapping_add(0x9e3779b97f4a7c15);
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    /// Creates a new RNG seeded by process arguments.
    pub fn new() -> Self {
        let mut hasher = DefaultHasher::new();
        for arg in std::env::args_os().skip(1) {
            arg.hash(&mut hasher);
        }
        let mut prev = hasher.finish();
        Self(std::array::from_fn(|_| {
            prev = Self::split_mix(prev);
            prev
        }))
    }
    /// Generates a random [`u64`].
    pub fn next_u64(&mut self) -> u64 {
        let [x, y, z, c] = &mut self.0;
        let t = x.wrapping_shl(58).wrapping_add(*c);
        *c = *x >> 6;
        *x = x.wrapping_add(t);
        if *x < t {
            *c += 1;
        }
        *z = z.wrapping_mul(6906969069).wrapping_add(1234567);
        *y ^= y.wrapping_shl(13);
        *y ^= *y >> 17;
        *y ^= y.wrapping_shl(43);
        x.wrapping_add(*y).wrapping_add(*z)
    }
    /// Generates a random [`u64`] in `range`.
    ///
    /// Panics if no number is present in the range.
    ///
    /// # Example
    ///
    /// ```
    /// # use testlib::Rng;
    /// let mut rng = Rng::new();
    /// let my_number = rng.next_range(12..13);
    /// assert!((12..13).contains(&my_number));
    /// ```
    pub fn next_range<Range: Borrow<Bounds>, Bounds: RangeBounds<u64> + Debug>(
        &mut self,
        range: Range,
    ) -> u64 {
        let range = range.borrow();
        let min = match range.start_bound() {
            Bound::Included(&min) => min,
            Bound::Excluded(&min) if min < u64::MAX => min + 1,
            Bound::Unbounded => 0,
            _ => quit!(
                Fail,
                "Expected an integer bound containing one or more integers, found {range:?}"
            ),
        };
        let max = match range.end_bound() {
            Bound::Included(&max) => max,
            Bound::Excluded(&max) if max > u64::MIN => max - 1,
            Bound::Unbounded => u64::MAX,
            _ => quit!(
                Fail,
                "Expected an integer bound containing one or more integers, found {range:?}"
            ),
        };
        if min > max {
            quit!(
                Fail,
                "Expected an integer bound containing one or more integers, found {range:?}"
            );
        }
        let len = max - min + 1;
        let next = (self.next_u64() as u128 * len as u128) >> 64;
        min + next as u64
    }
    /// Generates a random [`f64`] in interval `[0, 1)`.
    pub fn next_f64(&mut self) -> f64 {
        self.next_u64() as f64 * 5.42101086242752217003726400434970e-20
    }
    /// Generates a weighted random [`u64`] in range `range`, with weight `w`.
    ///
    /// Positive `w` means maximum of `w`+1 random values.
    /// Negative `w` means minimum of `w`+1 random values.
    pub fn wnext_range<Range: Borrow<Bounds>, Bounds: RangeBounds<u64> + Debug>(
        &mut self,
        range: Range,
        w: i32,
    ) -> u64 {
        let range = range.borrow();
        let min = match range.start_bound() {
            Bound::Included(&min) => min,
            Bound::Excluded(&min) if min < u64::MAX => min + 1,
            Bound::Unbounded => 0,
            _ => quit!(
                Fail,
                "Expected an integer bound containing one or more integers, found {range:?}"
            ),
        };
        let max = match range.end_bound() {
            Bound::Included(&max) => max,
            Bound::Excluded(&max) if max > u64::MIN => max - 1,
            Bound::Unbounded => u64::MAX,
            _ => quit!(
                Fail,
                "Expected an integer bound containing one or more integers, found {range:?}"
            ),
        };
        if min > max {
            quit!(
                Fail,
                "Expected an integer bound containing one or more integers, found {range:?}"
            );
        }
        if w.abs() < 25 {
            let mut r = self.next_range::<&Bounds, Bounds>(range);
            if w < 0 {
                for _ in 0..-w {
                    r = r.min(self.next_range::<&Bounds, Bounds>(range));
                }
            } else {
                for _ in 0..w {
                    r = r.max(self.next_range::<&Bounds, Bounds>(range));
                }
            }
            r
        } else {
            let p = if w < 0 {
                1.0 - self.next_f64().powf(1.0 / (-w + 1) as f64)
            } else {
                self.next_f64().powf(1.0 / (w + 1) as f64)
            };
            let len = (max - min + 1) as f64;
            (p * len).min(len).max(0.0) as u64
        }
    }
    pub fn shuffle<T>(&mut self, arr: &mut [T]) {
        for i in 0..arr.len() {
            let j = self.next_range(i as u64..arr.len() as u64) as usize;
            arr.swap(i, j);
        }
    }
}

/// Small regex subset.
///
/// Supported syntax:
/// - zero or one (`?`)
/// - range (`[a-z]`)
/// - count (`{5}`, `{1,3}`)
/// - any character (`.`)
/// - any times (`*`)
/// - one or more times (`+`)
/// - grouping (`()`)
#[derive(Debug)]
pub enum Regex {
    Raw(char),
    Question(Vec<Regex>),
    Range(Vec<(char, char)>),
    Count(Vec<Regex>, usize, usize),
    Any,
    Star(Vec<Regex>),
    Plus(Vec<Regex>),
    Group(Vec<Regex>),
}

impl FromStr for Regex {
    type Err = &'static str;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (span, group) = parse_group(s)?;
        if span == s.len() {
            Ok(Regex::Group(group))
        } else {
            Err("unexpected `)`.")
        }
    }
}

fn parse_group(mut s: &str) -> Result<(usize, Vec<Regex>), &'static str> {
    let mut stage = vec![];
    let mut iter = s.char_indices();
    let mut escaping = false;
    let mut span = 0;
    while let Some((i, c)) = iter.next() {
        match c {
            '(' if !escaping => {
                span += i + 1;
                let (gspan, group) = parse_group(&s[i + 1..])?;
                span += gspan + 1;
                s = &s[span..];
                stage.push(Regex::Group(group));
                iter = s.char_indices();
            }
            ')' if !escaping => {
                span += i;
                return Ok((span, stage));
            }
            '\\' if !escaping => {
                escaping = true;
            }
            '[' if !escaping => {
                span += i;
                let (rspan, range) = parse_range(&s[span..])?;
                span += rspan;
                s = &s[span..];
                iter = s.char_indices();
                stage.push(Regex::Range(range));
            }
            ']' if !escaping => {
                return Err("unexpected `]`.");
            }
            '{' if !escaping => {
                span += i;
                let (cspan, count) = parse_count(&s[span..])?;
                span += cspan;
                s = &s[span..];
                iter = s.char_indices();
                let last = stage.pop().ok_or("expected group or char.")?;
                match last {
                    Regex::Group(g) => {
                        stage.push(Regex::Count(g, count.0, count.1));
                    }
                    r @ (Regex::Raw(_) | Regex::Any) => {
                        stage.push(Regex::Count(vec![r], count.0, count.1));
                    }
                    _ => {
                        return Err("expected group or char.");
                    }
                }
            }
            '}' if !escaping => return Err("unexpected `}`."),
            '.' if !escaping => {
                stage.push(Regex::Any);
            }
            '*' if !escaping => {
                let last = stage.pop().ok_or("expected group or char.")?;
                match last {
                    Regex::Group(g) => {
                        stage.push(Regex::Star(g));
                    }
                    r @ (Regex::Raw(_) | Regex::Any) => {
                        stage.push(Regex::Star(vec![r]));
                    }
                    _ => {
                        return Err("expected group or char.");
                    }
                }
            }
            '+' if !escaping => {
                let last = stage.pop().ok_or("expected group or char.")?;
                match last {
                    Regex::Group(g) => {
                        stage.push(Regex::Plus(g));
                    }
                    r @ (Regex::Raw(_) | Regex::Any) => {
                        stage.push(Regex::Plus(vec![r]));
                    }
                    _ => {
                        return Err("expected group or char.");
                    }
                }
            }
            '?' if !escaping => {
                let last = stage.pop().ok_or("expected group or char.")?;
                match last {
                    Regex::Group(g) => {
                        stage.push(Regex::Question(g));
                    }
                    r @ (Regex::Raw(_) | Regex::Any | Regex::Plus(_)) => {
                        stage.push(Regex::Question(vec![r]));
                    }
                    _ => {
                        return Err("expected group or char.");
                    }
                }
            }
            _ => {
                stage.push(Regex::Raw(c));
                escaping = false;
            }
        }
    }
    span += s.len();
    Ok((span, stage))
}

fn parse_range(s: &str) -> Result<(usize, Vec<(char, char)>), &'static str> {
    let Some((leading, s)) = s.split_once('[') else {
        return Err("expected `[`.");
    };
    if !leading.is_empty() {
        return Err("expected `[`.");
    }
    let mut escaping = false;
    let mut ranges = vec![];
    let mut expect_second = false;
    for (i, c) in s.char_indices() {
        match c {
            ']' if !escaping => {
                if expect_second {
                    return Err("expected char, found `]`.");
                }
                // (i + 1) + 1 (length of '[')
                return Ok((i + 2, ranges));
            }
            '\\' if !escaping => {
                escaping = true;
            }
            '-' if !escaping => {
                expect_second = true;
            }
            _ if expect_second => {
                let Some(last) = ranges.last_mut() else {
                    return Err("expected char, found `-`.");
                };
                last.1 = c;
                escaping = false;
                expect_second = false;
            }
            _ => {
                ranges.push((c, c));
                escaping = false;
            }
        }
    }
    Err("expected `]`.")
}

fn parse_count(s: &str) -> Result<(usize, (usize, usize)), &'static str> {
    let Some((leading, s)) = s.split_once('{') else {
        return Err("expected `{`.");
    };
    if !leading.is_empty() {
        return Err("expected `{`.");
    }
    let Some((s, _)) = s.split_once('}') else {
        return Err("expected `}`.");
    };
    let span = s.len() + 2;
    let count = if let Some((low, high)) = s.split_once(',') {
        let low = if low.is_empty() {
            0
        } else {
            low.parse::<usize>().ok().ok_or("expected number.")?
        };
        let high = if high.is_empty() {
            usize::MAX
        } else {
            high.parse::<usize>().ok().ok_or("expected number.")?
        };
        (low, high)
    } else {
        let exact = s.parse::<usize>().ok().ok_or("expected number.")?;
        (exact, exact)
    };
    Ok((span, count))
}
