// Minimal Parquet writer: one row group, PLAIN encoding, uncompressed, one data page per column.
pub struct Tw {
    pub b: Vec<u8>,
    stack: Vec<i16>,
    cur: i16,
}
fn varint(b: &mut Vec<u8>, mut v: u64) {
    while v >= 0x80 {
        b.push((v as u8) | 0x80);
        v >>= 7;
    }
    b.push(v as u8);
}
fn zz(v: i64) -> u64 {
    ((v << 1) ^ (v >> 63)) as u64
}
impl Tw {
    pub fn new() -> Tw {
        Tw { b: Vec::new(), stack: Vec::new(), cur: 0 }
    }
    fn fh(&mut self, id: i16, ty: u8) {
        let d = id - self.cur;
        if d > 0 && d <= 15 {
            self.b.push(((d as u8) << 4) | ty);
        } else {
            self.b.push(ty);
            varint(&mut self.b, zz(id as i64));
        }
        self.cur = id;
    }
    pub fn i32f(&mut self, id: i16, v: i32) {
        self.fh(id, 5);
        varint(&mut self.b, zz(v as i64));
    }
    pub fn i64f(&mut self, id: i16, v: i64) {
        self.fh(id, 6);
        varint(&mut self.b, zz(v));
    }
    pub fn strf(&mut self, id: i16, s: &str) {
        self.fh(id, 8);
        varint(&mut self.b, s.len() as u64);
        self.b.extend_from_slice(s.as_bytes());
    }
    pub fn list(&mut self, id: i16, ety: u8, n: usize) {
        self.fh(id, 9);
        if n < 15 {
            self.b.push(((n as u8) << 4) | ety);
        } else {
            self.b.push(0xF0 | ety);
            varint(&mut self.b, n as u64);
        }
    }
    pub fn list_i32_elem(&mut self, v: i32) {
        varint(&mut self.b, zz(v as i64));
    }
    pub fn list_str_elem(&mut self, s: &str) {
        varint(&mut self.b, s.len() as u64);
        self.b.extend_from_slice(s.as_bytes());
    }
    pub fn sbegin_field(&mut self, id: i16) {
        self.fh(id, 12);
        self.stack.push(self.cur);
        self.cur = 0;
    }
    pub fn sbegin_elem(&mut self) {
        self.stack.push(self.cur);
        self.cur = 0;
    }
    pub fn send(&mut self) {
        self.b.push(0);
        self.cur = self.stack.pop().unwrap();
    }
}

#[derive(Clone, Copy, PartialEq)]
pub enum Kind {
    Str,
    Date,
    I32,
    I64,
}
pub struct Spec {
    pub name: &'static str,
    pub kind: Kind,
    pub optional: bool,
}
pub struct Page {
    pub data: Vec<u8>,
    pub nvals: usize,
}

pub fn str_page(vals: impl Iterator<Item = &'static [u8]>, n: usize) -> Page {
    let mut data = Vec::with_capacity(n * 14);
    for s in vals {
        data.extend_from_slice(&(s.len() as u32).to_le_bytes());
        data.extend_from_slice(s);
    }
    Page { data, nvals: n }
}
pub fn i32_page(v: &[i32]) -> Page {
    let mut data = Vec::with_capacity(v.len() * 4);
    for x in v {
        data.extend_from_slice(&x.to_le_bytes());
    }
    Page { data, nvals: v.len() }
}
pub fn i64_page(v: &[i64]) -> Page {
    let mut data = Vec::with_capacity(v.len() * 8);
    for x in v {
        data.extend_from_slice(&x.to_le_bytes());
    }
    Page { data, nvals: v.len() }
}
/// optional string page: `vals[i] == None` is null.
pub fn opt_str_page(vals: &[Option<&'static [u8]>]) -> Page {
    let n = vals.len();
    let groups = (n + 7) / 8;
    let mut rle = Vec::new();
    varint(&mut rle, ((groups as u64) << 1) | 1);
    let base = rle.len();
    rle.resize(base + groups, 0);
    for (i, v) in vals.iter().enumerate() {
        if v.is_some() {
            rle[base + i / 8] |= 1 << (i % 8);
        }
    }
    let mut data = Vec::new();
    data.extend_from_slice(&(rle.len() as u32).to_le_bytes());
    data.extend_from_slice(&rle);
    for s in vals.iter().flatten() {
        data.extend_from_slice(&(s.len() as u32).to_le_bytes());
        data.extend_from_slice(s);
    }
    Page { data, nvals: n }
}

pub fn file_bytes(specs: &[Spec], pages: &[Page], nrows: usize) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::with_capacity(pages.iter().map(|p| p.data.len() + 64).sum::<usize>() + 4096);
    out.extend_from_slice(b"PAR1");
    let mut chunks = Vec::new(); // (offset, size, nvals)
    for p in pages {
        let off = out.len();
        let mut h = Tw::new();
        h.i32f(1, 0);
        h.i32f(2, p.data.len() as i32);
        h.i32f(3, p.data.len() as i32);
        h.sbegin_field(5);
        h.i32f(1, p.nvals as i32);
        h.i32f(2, 0);
        h.i32f(3, 3);
        h.i32f(4, 3);
        h.send();
        h.b.push(0);
        out.extend_from_slice(&h.b);
        out.extend_from_slice(&p.data);
        chunks.push((off, out.len() - off, p.nvals));
    }
    let ptype = |k: Kind| match k {
        Kind::Str => 6,
        Kind::Date | Kind::I32 => 1,
        Kind::I64 => 2,
    };
    let mut t = Tw::new();
    t.i32f(1, 1);
    t.list(2, 12, specs.len() + 1);
    t.sbegin_elem();
    t.strf(4, "schema");
    t.i32f(5, specs.len() as i32);
    t.send();
    for s in specs {
        t.sbegin_elem();
        t.i32f(1, ptype(s.kind));
        t.i32f(3, if s.optional { 1 } else { 0 });
        t.strf(4, s.name);
        match s.kind {
            Kind::Str => {
                t.i32f(6, 0);
                t.sbegin_field(10);
                t.sbegin_field(1);
                t.send();
                t.send();
            }
            Kind::Date => {
                t.i32f(6, 6);
                t.sbegin_field(10);
                t.sbegin_field(6);
                t.send();
                t.send();
            }
            _ => {}
        }
        t.send();
    }
    t.i64f(3, nrows as i64);
    t.list(4, 12, 1);
    t.sbegin_elem();
    t.list(1, 12, specs.len());
    let mut total = 0usize;
    for (i, s) in specs.iter().enumerate() {
        let (off, size, nv) = chunks[i];
        total += size;
        t.sbegin_elem();
        t.i64f(2, off as i64);
        t.sbegin_field(3);
        t.i32f(1, ptype(s.kind));
        t.list(2, 5, if s.optional { 2 } else { 1 });
        t.list_i32_elem(0);
        if s.optional {
            t.list_i32_elem(3);
        }
        t.list(3, 8, 1);
        t.list_str_elem(s.name);
        t.i32f(4, 0);
        t.i64f(5, nv as i64);
        t.i64f(6, size as i64);
        t.i64f(7, size as i64);
        t.i64f(9, off as i64);
        t.send();
        t.send();
    }
    t.i64f(2, total as i64);
    t.i64f(3, nrows as i64);
    t.send();
    t.strf(6, "shopping-sessions-rs");
    t.b.push(0);
    out.extend_from_slice(&t.b);
    out.extend_from_slice(&(t.b.len() as u32).to_le_bytes());
    out.extend_from_slice(b"PAR1");
    out
}
