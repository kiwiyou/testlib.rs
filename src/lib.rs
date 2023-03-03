use std::{
    borrow::Borrow,
    collections::hash_map::DefaultHasher,
    fmt::Debug,
    hash::{Hash, Hasher},
    io::Read,
    ops::{Bound, RangeBounds},
    str::FromStr,
};

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
            panic!("{name}: expected integer, found EOF");
        }
        // Safety guarantee: s only contains b'-' and b'0'..=b'9'.
        let s = unsafe { String::from_utf8_unchecked(s) };
        match s.parse() {
            Ok(v) if range.contains(&v) => v,
            _ => panic!("{name}: expected integer in bound {range:?}, found {s:?}"),
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
            panic!(
                "[LINE #{}] expected space, found {:?}",
                self.line,
                ch.map(|b| b as char)
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
            panic!("{name}: expected string, found EOF");
        }
        match String::from_utf8(s) {
            Ok(s) => s,
            Err(_) => panic!("{name}: invalid utf-8 string"),
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
            panic!("{name}: expected string, found EOF");
        }
        match String::from_utf8(s) {
            Ok(s) => s,
            Err(_) => panic!("{name}: invalid utf-8 string"),
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
                    panic!("[LINE #{}] expected EOLN, found {:?}", self.line, '\r');
                }
            }
            Some(b'\n') => {
                self.front += 1;
                self.line += 1;
            }
            None => {
                panic!("[LINE #{}] expected EOLN, found EOF", self.line);
            }
            Some(other) => {
                panic!(
                    "[LINE #{}] expected EOLN, found {:?}",
                    self.line, other as char
                );
            }
        }
    }
    /// Checks for EOF, panics if not found.
    pub fn read_eof(&mut self) {
        if let Some(ch) = self.read_byte() {
            panic!("[LINE #{}] expected EOF, found {:?}", self.line, ch as char);
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
            _ => panic!("No matching integers in bound {range:?}"),
        };
        let max = match range.end_bound() {
            Bound::Included(&max) => max,
            Bound::Excluded(&max) if max > u64::MIN => max - 1,
            Bound::Unbounded => u64::MAX,
            _ => panic!("No matching integers in bound {range:?}"),
        };
        if min > max {
            panic!("No matching integers in bound {range:?}");
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
            _ => panic!("No matching integers in bound {range:?}"),
        };
        let max = match range.end_bound() {
            Bound::Included(&max) => max,
            Bound::Excluded(&max) if max > u64::MIN => max - 1,
            Bound::Unbounded => u64::MAX,
            _ => panic!("No matching integers in bound {range:?}"),
        };
        if min > max {
            panic!("No matching integers in bound {range:?}");
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

/*
WORKING IN PROGRESS
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
pub enum Regex {
    Raw(String),
    Question(Vec<Regex>),
    Range(Vec<(char, char)>),
    Count(Vec<Regex>, usize, usize),
    Any,
    Star(Vec<Regex>),
    Plus(Vec<Regex>),
}

impl FromStr for Regex {
    type Err = &'static str;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut stack = vec![];
        let mut escaping = false;
        enum State {
            Raw(String),
            RangeBegin,
            RangeElement(Vec<(char, char)>,
        }
        let mut state = State::Raw;
        for c in s.chars() {
            if escaping {
                match &mut state {
                    State::Raw(buf) => buf.push(c),
                }
            }
            match (&mut state, c) {

            }
        }
    }
}
*/
