mod pq;
use memmap2::Mmap;
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

const DAY: i64 = 86_400_000;
const WEEK: i64 = 604_800_000;
const GAP: i64 = 1_800_000;
const NP: usize = 256;
type B = &'static [u8];

// ---------- hashing ----------
#[inline(always)]
fn mix(a: u64, b: u64) -> u64 {
    let r = (a as u128).wrapping_mul(b as u128);
    (r as u64) ^ ((r >> 64) as u64)
}
#[inline]
fn hash(b: &[u8]) -> u64 {
    const P0: u64 = 0xa076_1d64_78bd_642f;
    const P1: u64 = 0xe703_7ed1_a0b4_28db;
    const P2: u64 = 0x8ebc_6af0_9c88_c6e3;
    let l = b.len();
    let mut s = P0 ^ (l as u64).wrapping_mul(P2);
    let rd8 = |i: usize| u64::from_le_bytes(b[i..i + 8].try_into().unwrap());
    let rd4 = |i: usize| u32::from_le_bytes(b[i..i + 4].try_into().unwrap()) as u64;
    if l >= 8 {
        let mut i = 0;
        while i + 8 < l {
            s = mix(s ^ rd8(i), P1);
            i += 8;
        }
        s = mix(s ^ rd8(l - 8), P2);
    } else if l >= 4 {
        s = mix(s ^ rd4(0) ^ (rd4(l - 4) << 32), P2);
    } else if l > 0 {
        let w = (b[0] as u64) | ((b[l / 2] as u64) << 8) | ((b[l - 1] as u64) << 16);
        s = mix(s ^ w, P2);
    }
    let h = mix(s, P1 ^ 0x55);
    if h == 0 { 1 } else { h }
}
#[derive(Default)]
struct IdH(u64);
impl Hasher for IdH {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        unreachable!()
    }
    fn write_u64(&mut self, v: u64) {
        self.0 = v;
    }
}
type HM<V> = HashMap<u64, V, BuildHasherDefault<IdH>>;

#[inline]
fn pack(s: &[u8]) -> u64 {
    (s.as_ptr() as u64) | ((s.len() as u64) << 48)
}
#[inline]
fn unpack(p: u64) -> B {
    unsafe { std::slice::from_raw_parts((p & 0xFFFF_FFFF_FFFF) as *const u8, (p >> 48) as usize) }
}

// ---------- parsing ----------
#[inline]
fn split<const N: usize>(line: B) -> Option<[B; N]> {
    let mut out: [B; N] = [&line[0..0]; N];
    let mut n = 0;
    let mut start = 0;
    for (i, &c) in line.iter().enumerate() {
        if c == b',' {
            if n + 1 >= N {
                return None;
            }
            out[n] = &line[start..i];
            n += 1;
            start = i + 1;
        }
    }
    if n + 1 != N {
        return None;
    }
    out[n] = &line[start..];
    for f in out.iter_mut() {
        if f.contains(&b'"') {
            let l = f.len();
            if l < 2 || f[0] != b'"' || f[l - 1] != b'"' || f[1..l - 1].contains(&b'"') {
                return None;
            }
            *f = &f[1..l - 1];
        }
    }
    Some(out)
}
#[inline]
fn d2(b: &[u8]) -> Option<i64> {
    let (x, y) = (b[0].wrapping_sub(b'0'), b[1].wrapping_sub(b'0'));
    if x > 9 || y > 9 { None } else { Some((x * 10 + y) as i64) }
}
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}
/// "YYYY-MM-DD" (first 10 bytes of `f`) -> days since the epoch, None if not a valid calendar date.
fn parse_date(f: &[u8]) -> Option<i64> {
    if f.len() < 10 || f[4] != b'-' || f[7] != b'-' {
        return None;
    }
    let y = d2(&f[0..2])? * 100 + d2(&f[2..4])?;
    let mo = d2(&f[5..7])?;
    let d = d2(&f[8..10])?;
    if !(1..=12).contains(&mo) || d < 1 {
        return None;
    }
    let leap = (y % 4 == 0 && y % 100 != 0) || y % 400 == 0;
    let dim = match mo {
        2 => if leap { 29 } else { 28 },
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    };
    if d > dim {
        return None;
    }
    Some(days_from_civil(y, mo, d))
}
/// Small direct-mapped cache: validated date text -> days. A window has few distinct dates.
struct DateCache {
    k1: [u64; 64],
    k2: [u16; 64],
    days: [i32; 64],
}
impl DateCache {
    fn new() -> Self {
        DateCache { k1: [0; 64], k2: [0; 64], days: [i32::MIN; 64] }
    }
    #[inline(always)]
    fn get(&mut self, f: &[u8]) -> Option<i64> {
        let a = u64::from_le_bytes(f[0..8].try_into().unwrap());
        let b = u16::from_le_bytes(f[8..10].try_into().unwrap());
        let h = ((a ^ (b as u64).wrapping_mul(0xff51_afd7_ed55_8ccd)).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 58) as usize;
        if self.k1[h] == a && self.k2[h] == b && self.days[h] != i32::MIN {
            return Some(self.days[h] as i64);
        }
        let d = parse_date(f)?;
        self.k1[h] = a;
        self.k2[h] = b;
        self.days[h] = d as i32;
        Some(d)
    }
}
fn parse_ts(f: &[u8]) -> Option<i64> {
    parse_ts_c(f, &mut DateCache::new())
}
#[inline(always)]
fn parse_ts_c(f: &[u8], dc: &mut DateCache) -> Option<i64> {
    let l = f.len();
    if (l == 20 && f[19] == b'Z') || (l == 25 && (f[19] == b'+' || f[19] == b'-')) {
        if f[10] != b'T' || f[13] != b':' || f[16] != b':' {
            return None;
        }
        let days = dc.get(f)?;
        let hh = d2(&f[11..13])?;
        let mi = d2(&f[14..16])?;
        let ss = d2(&f[17..19])?;
        if hh > 23 || mi > 59 || ss > 59 {
            return None;
        }
        let mut t = (days * 86400 + hh * 3600 + mi * 60 + ss) * 1000;
        if l == 25 {
            if f[22] != b':' {
                return None;
            }
            let oh = d2(&f[20..22])?;
            let om = d2(&f[23..25])?;
            if oh > 23 || om > 59 {
                return None;
            }
            let off = (oh * 60 + om) * 60_000;
            if f[19] == b'+' { t -= off } else { t += off }
        }
        return Some(t);
    }
    if l == 0 {
        return None;
    }
    let mut v: u64 = 0;
    for &c in f {
        let d = c.wrapping_sub(b'0');
        if d > 9 {
            return None;
        }
        v = v.checked_mul(10)?.checked_add(d as u64)?;
    }
    if v > i64::MAX as u64 { None } else { Some(v as i64) }
}
fn parse_price(f: &[u8]) -> Option<u32> {
    if f.is_empty() {
        return None;
    }
    let mut v: u64 = 0;
    for &c in f {
        let d = c.wrapping_sub(b'0');
        if d > 9 {
            return None;
        }
        v = (v * 10 + d as u64).min(10_000_001);
    }
    if (1..=10_000_000).contains(&v) { Some(v as u32) } else { None }
}

// ---------- files ----------
fn list_csv(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = match std::fs::read_dir(dir) {
        Ok(rd) => rd
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| p.extension().map_or(false, |x| x == "csv") && p.is_file())
            .collect(),
        Err(_) => vec![],
    };
    v.sort();
    v
}
fn map_file(p: &Path) -> B {
    let f = std::fs::File::open(p).expect("open");
    let len = f.metadata().unwrap().len();
    if len == 0 {
        return &[];
    }
    let m = unsafe { Mmap::map(&f).expect("mmap") };
    let m: &'static Mmap = Box::leak(Box::new(m));
    &m[..]
}
fn read_small(p: &Path) -> B {
    Box::leak(std::fs::read(p).expect("read").into_boxed_slice())
}
/// Split files into line-aligned chunks (header skipped).
fn chunks(files: &[B], target: usize) -> Vec<(usize, usize, usize)> {
    let mut v = vec![];
    for (fi, d) in files.iter().enumerate() {
        if d.is_empty() {
            continue;
        }
        let mut pos = match memchr::memchr(b'\n', d) {
            Some(i) => i + 1,
            None => continue,
        };
        while pos < d.len() {
            let ne = (pos + target).min(d.len());
            let end = if ne == d.len() {
                ne
            } else {
                match memchr::memchr(b'\n', &d[ne..]) {
                    Some(i) => ne + i + 1,
                    None => d.len(),
                }
            };
            v.push((fi, pos, end));
            pos = end;
        }
    }
    v.sort_by_key(|&(_, s, e)| std::cmp::Reverse(e - s));
    v
}
#[inline]
fn for_lines(d: B, mut f: impl FnMut(B)) {
    let mut p = 0;
    while p < d.len() {
        match memchr::memchr(b'\n', &d[p..]) {
            Some(i) => {
                f(&d[p..p + i]);
                p += i + 1;
            }
            None => {
                f(&d[p..]);
                break;
            }
        }
    }
}


// ---------- fast line scanner ----------
#[derive(Default)]
struct Scratch {
    cm: Vec<u32>,
    nl: Vec<u32>,
    /// cumulative count of '"' bytes before each newline
    nq: Vec<u32>,
}
#[inline(always)]
fn push_bits(out: &mut Vec<u32>, mut m: u32, base: u32) {
    while m != 0 {
        out.push(base + m.trailing_zeros());
        m &= m - 1;
    }
}
fn scan(d: &[u8], sc: &mut Scratch) {
    use std::arch::x86_64::*;
    sc.cm.clear();
    sc.nl.clear();
    sc.nq.clear();
    let n = d.len();
    let mut i = 0usize;
    let mut qrun = 0u32;
    // SAFETY: AVX2 is enabled for the whole crate via target-cpu=x86-64-v3 (.cargo/config.toml);
    // every 32-byte load is at offset i with i + 32 <= n, so it stays inside `d`.
    unsafe {
        let vc = _mm256_set1_epi8(b',' as i8);
        let vn = _mm256_set1_epi8(b'\n' as i8);
        let vq = _mm256_set1_epi8(b'"' as i8);
        while i + 32 <= n {
            let v = _mm256_loadu_si256(d.as_ptr().add(i) as *const __m256i);
            let mc = _mm256_movemask_epi8(_mm256_cmpeq_epi8(v, vc)) as u32;
            let mut mn = _mm256_movemask_epi8(_mm256_cmpeq_epi8(v, vn)) as u32;
            let mq = _mm256_movemask_epi8(_mm256_cmpeq_epi8(v, vq)) as u32;
            push_bits(&mut sc.cm, mc, i as u32);
            while mn != 0 {
                let k = mn.trailing_zeros();
                sc.nl.push(i as u32 + k);
                sc.nq.push(qrun + (mq & ((1u32 << k) - 1)).count_ones());
                mn &= mn - 1;
            }
            qrun += mq.count_ones();
            i += 32;
        }
    }
    while i < n {
        match d[i] {
            b',' => sc.cm.push(i as u32),
            b'\n' => {
                sc.nl.push(i as u32);
                sc.nq.push(qrun);
            }
            b'"' => qrun += 1,
            _ => {}
        }
        i += 1;
    }
}
/// Calls `f` with the N unquoted fields of every well-formed line of `d` (header already skipped).
#[inline(always)]
fn lines<const N: usize>(d: B, sc: &mut Scratch, mut f: impl FnMut([B; N])) {
    let last = match memchr::memrchr(b'\n', d) {
        Some(i) => i + 1,
        None => 0,
    };
    if last > 0 {
        let body = &d[..last];
        scan(body, sc);
        let (cm, nl, nq) = (&sc.cm, &sc.nl, &sc.nq);
        let (mut ci, mut ls, mut pq_) = (0usize, 0usize, 0u32);
        for (li, &e) in nl.iter().enumerate() {
            let e = e as usize;
            let qc = (nq[li] - pq_) as usize;
            pq_ = nq[li];
            // commas of this line
            let ok = ci + N - 1 <= cm.len()
                && (N == 1 || (cm[ci + N - 2] as usize) < e)
                && (ci + N - 1 >= cm.len() || (cm[ci + N - 1] as usize) > e);
            if ok {
                let mut fs: [B; N] = [&d[0..0]; N];
                let mut s = ls;
                let mut quoted = 0usize;
                let mut good = true;
                for j in 0..N {
                    let fe = if j + 1 < N { cm[ci + j] as usize } else { e };
                    let raw = &d[s..fe];
                    s = fe + 1;
                    if !raw.is_empty() && raw[0] == b'"' {
                        let l = raw.len();
                        if l >= 2 && raw[l - 1] == b'"' {
                            fs[j] = &raw[1..l - 1];
                            quoted += 2;
                        } else {
                            good = false;
                        }
                    } else {
                        fs[j] = raw;
                    }
                }
                ci += N - 1;
                if good && qc == quoted {
                    f(fs);
                }
            } else {
                while ci < cm.len() && (cm[ci] as usize) < e {
                    ci += 1;
                }
            }
            ls = e + 1;
        }
    }
    if last < d.len() {
        if let Some(fs) = split::<N>(&d[last..]) {
            f(fs);
        }
    }
}
fn populate(d: &[u8]) {
    let a = d.as_ptr() as usize & !4095;
    let l = d.as_ptr() as usize + d.len() - a;
    unsafe {
        libc::madvise(a as *mut libc::c_void, l, 22); // MADV_POPULATE_READ
    }
}

fn par<S: Send>(nt: usize, ntasks: usize, init: impl Fn() -> S + Sync, f: impl Fn(&mut S, usize) + Sync) -> Vec<S> {
    let ctr = AtomicUsize::new(0);
    let prof = std::env::var("SS_TASKS").is_ok();
    let t_start = Instant::now();
    let durs: std::sync::Mutex<Vec<(f64, usize)>> = std::sync::Mutex::new(Vec::new());
    let res = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..nt)
            .map(|_| {
                sc.spawn(|| {
                    let mut s = init();
                    let mut mine: Vec<(f64, usize)> = Vec::new();
                    loop {
                        let t = ctr.fetch_add(1, Ordering::Relaxed);
                        if t >= ntasks {
                            break;
                        }
                        if prof {
                            let t0 = Instant::now();
                            f(&mut s, t);
                            mine.push((t0.elapsed().as_secs_f64(), t));
                        } else {
                            f(&mut s, t);
                        }
                    }
                    if prof {
                        durs.lock().unwrap().extend(mine);
                    }
                    s
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    if prof {
        let mut d = durs.into_inner().unwrap();
        d.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
        let sum: f64 = d.iter().map(|x| x.0).sum();
        eprintln!(
            "  par: {} tasks, wall {:.3}s, sum {:.3}s (ideal {:.3}s), top tasks: {}",
            ntasks,
            t_start.elapsed().as_secs_f64(),
            sum,
            sum / nt as f64,
            d.iter().take(3).map(|x| format!("#{}={:.0}ms", x.1, x.0 * 1e3)).collect::<Vec<_>>().join(" ")
        );
    }
    res
}

// ---------- link table ----------
struct LinkTab {
    mask: usize,
    keys: Vec<u64>,
    vals: Vec<[u64; 2]>, // person key, name ptr
}
impl LinkTab {
    #[inline(always)]
    fn prefetch(&self, h: u64) {
        unsafe {
            let i = (h as usize) & self.mask;
            std::arch::x86_64::_mm_prefetch(self.keys.as_ptr().add(i) as *const i8, std::arch::x86_64::_MM_HINT_T0);
        }
    }
    #[inline]
    fn get(&self, h: u64) -> Option<[u64; 2]> {
        let mut i = (h as usize) & self.mask;
        loop {
            let k = unsafe { *self.keys.get_unchecked(i) };
            if k == h {
                return Some(unsafe { *self.vals.get_unchecked(i) });
            }
            if k == 0 {
                return None;
            }
            i = (i + 1) & self.mask;
        }
    }
}
fn find(p: &mut [u32], mut x: u32) -> u32 {
    while p[x as usize] != x {
        let g = p[p[x as usize] as usize];
        p[x as usize] = g;
        x = g;
    }
    x
}
fn build_links(files: &[B], nt: usize) -> LinkTab {
    let ch = chunks(files, 8 << 20);
    let res = par(nt, ch.len(), || (Scratch::default(), Vec::<(B, B)>::new()), |st, t| {
        let (fi, s, e) = ch[t];
        let (sc, out) = st;
        lines::<2>(&files[fi][s..e], sc, |[a, b]| {
            if !a.is_empty() && !b.is_empty() {
                out.push((a, b));
            }
        });
    });
    let res: Vec<Vec<(B, B)>> = res.into_iter().map(|x| x.1).collect();
    let mut idx: HM<u32> = HM::default();
    let mut names: Vec<B> = vec![];
    let mut parent: Vec<u32> = vec![];
    let mut hs: Vec<u64> = vec![];
    let mut intern = |s: B, idx: &mut HM<u32>| -> u32 {
        let h = hash(s);
        *idx.entry(h).or_insert_with(|| {
            names.push(s);
            parent.push(names.len() as u32 - 1);
            hs.push(h);
            names.len() as u32 - 1
        })
    };
    let mut edges = vec![];
    for v in &res {
        for &(a, b) in v {
            let x = intern(a, &mut idx);
            let y = intern(b, &mut idx);
            edges.push((x, y));
        }
    }
    drop(intern);
    for (x, y) in edges {
        let rx = find(&mut parent, x);
        let ry = find(&mut parent, y);
        if rx != ry {
            parent[rx.max(ry) as usize] = rx.min(ry);
        }
    }
    let n = names.len();
    let mut best: Vec<u32> = (0..n as u32).collect();
    for i in 0..n {
        let r = find(&mut parent, i as u32) as usize;
        if names[i] < names[best[r] as usize] {
            best[r] = i as u32;
        }
    }
    let cap = (n * 2 + 2).next_power_of_two();
    let mut t = LinkTab { mask: cap - 1, keys: vec![0; cap], vals: vec![[0, 0]; cap] };
    for i in 0..n {
        let r = find(&mut parent, i as u32) as usize;
        let nm = names[best[r] as usize];
        let mut j = (hs[i] as usize) & t.mask;
        while t.keys[j] != 0 {
            j = (j + 1) & t.mask;
        }
        t.keys[j] = hs[i];
        t.vals[j] = [hash(nm), pack(nm)];
    }
    t
}

// ---------- records ----------
#[derive(Clone, Copy)]
struct Ev1 {
    id: u64,
    user: u64,
    ts: i64,
    ing: i64,
    uptr: u64,
    price: u32,
    cat: u8,
    kind: u8,
    valid: bool,
}
#[derive(Clone, Copy)]
struct Pe {
    key: u64,
    ts: i64,
    name: u64,
    price: u32,
    cat: u8,
    kind: u8,
}
#[derive(Clone, Copy)]
struct Ck {
    key: u64,
    ts: i64,
    cid: u64,
    camp: u32,
}

struct Small {
    m: HM<u32>,
    names: Vec<B>,
}
impl Small {
    fn get(&self, f: &[u8]) -> Option<u32> {
        let i = *self.m.get(&hash(f))?;
        if self.names[i as usize] == f { Some(i) } else { None }
    }
}

#[inline(always)]
fn make_ev(f: [B; 7], ws: i64, we: i64, products: &Small, pcat: &[u8], unknown_cat: u8, dc: &mut DateCache) -> Option<Ev1> {
    let [id, user, ts, ing, ty, pr, price] = f;
    if id.is_empty() {
        return None;
    }
    let ing = parse_ts_c(ing, dc).unwrap_or(i64::MAX);
    let tsv = parse_ts_c(ts, dc);
    let mut valid = false;
    let mut kind = 0u8;
    let mut cat = 0u8;
    let mut pv = 0u32;
    let mut tsx = 0;
    if let Some(t) = tsv {
        tsx = t;
        if t >= ws && t < we && !user.is_empty() && !pr.is_empty() && ing != i64::MAX && ing - t <= DAY {
            match ty {
                b"view" => valid = true,
                b"cart" => {
                    kind = 1;
                    valid = true
                }
                b"purchase" => {
                    kind = 2;
                    if let Some(p) = parse_price(price) {
                        pv = p;
                        valid = true;
                        cat = products.get(pr).map_or(unknown_cat, |i| pcat[i as usize]);
                    }
                }
                _ => {}
            }
        }
    }
    Some(Ev1 { id: hash(id), user: hash(user), ts: tsx, ing, uptr: pack(user), price: pv, cat, kind, valid })
}

/// Append-only list stored as fixed-size blocks: no reallocation or copying as it grows.
struct Blocks<T> {
    full: Vec<Vec<T>>,
    cur: Vec<T>,
    blk: usize,
}
impl<T> Blocks<T> {
    fn new(blk: usize) -> Self {
        Blocks { full: Vec::new(), cur: Vec::new(), blk }
    }
    #[inline(always)]
    fn push(&mut self, v: T) {
        if self.cur.len() == self.cur.capacity() {
            self.roll();
        }
        self.cur.push(v);
    }
    #[cold]
    fn roll(&mut self) {
        let old = std::mem::replace(&mut self.cur, Vec::with_capacity(self.blk));
        if !old.is_empty() {
            self.full.push(old);
        }
    }
    fn len(&self) -> usize {
        self.full.iter().map(|b| b.len()).sum::<usize>() + self.cur.len()
    }
    fn slices(&self) -> impl Iterator<Item = &[T]> {
        self.full.iter().map(|b| &b[..]).chain(std::iter::once(&self.cur[..]))
    }
}
fn new_blocks<T>(blk: usize) -> Vec<Blocks<T>> {
    (0..NP).map(|_| Blocks::new(blk)).collect()
}
const EV_BLK: usize = 2048; // 48 B records -> 96 KB blocks
const PE_BLK: usize = 3072; // 32 B records -> 96 KB blocks

fn json_str(j: &str, key: &str) -> String {
    let i = j.find(&format!("\"{}\"", key)).expect("manifest key");
    let r = &j[i + key.len() + 2..];
    let a = r.find('"').unwrap() + 1;
    let r = &r[a..];
    r[..r.find('"').unwrap()].to_string()
}

fn write_file(dir: &Path, name: &str, bytes: Vec<u8>) {
    std::fs::write(dir.join(name), bytes).expect("write");
}

/// Adds one assist to every session (grouped by day) whose start lies in [a, b].
#[allow(clippy::too_many_arguments)]
fn add_interval(acc: &mut [[u64; 4]], nd: usize, sw_start: &[i64], sw_day: &[u32], day_first: &[u32], c: usize, a: i64, b: i64) {
    let lo_i = sw_start.partition_point(|&s| s < a);
    let hi_i = sw_start.partition_point(|&s| s <= b);
    if lo_i >= hi_i {
        return;
    }
    let (d0, d1) = (sw_day[lo_i] as usize, sw_day[hi_i - 1] as usize);
    for d in d0..=d1 {
        let l = lo_i.max(day_first[d] as usize);
        let h = hi_i.min(day_first[d + 1] as usize);
        if h > l {
            acc[c * nd + d][3] += (h - l) as u64;
        }
    }
}
static FILE_ID: AtomicUsize = AtomicUsize::new(0);
const FLUSH_ROWS: usize = 49_152;

#[allow(clippy::too_many_arguments)]
fn flush_users(dir: &Path, specs: &[pq::Spec], cats: &[B], name: &[u64], day: &[i32], sess: &[i32], ev: &[i32], rev: &[i64], top: &[u8]) {
    let n = name.len();
    let tops: Vec<Option<B>> = top.iter().map(|&t| if t == 255 { None } else { Some(cats[t as usize]) }).collect();
    let pages = [
        pq::str_page(name.iter().map(|&p| unpack(p)), n),
        pq::i32_page(day),
        pq::i32_page(sess),
        pq::i32_page(ev),
        pq::i64_page(rev),
        pq::opt_str_page(&tops),
    ];
    let id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    write_file(dir, &format!("part-{:05}.parquet", id), pq::file_bytes(specs, &pages, n));
}
struct WhaleTimer(Option<Instant>, usize, usize);
impl Drop for WhaleTimer {
    fn drop(&mut self) {
        if let Some(t) = self.0 {
            eprintln!("whale: {} events {} clicks -> {:.1} ms", self.1, self.2, t.elapsed().as_secs_f64() * 1e3);
        }
    }
}
struct S2 {
    out: Vec<Blocks<Pe>>,
    v: Vec<Ev1>,
    tab: Vec<u64>,
    surv: Vec<u32>,
}
#[derive(Default)]
struct Grp {
    tkey: Vec<u64>,
    tgid: Vec<u32>,
    evg: Vec<u32>,
    cnt: Vec<u32>,
    start: Vec<u32>,
    cur: Vec<u32>,
    sev: Vec<Pe>,
    cgid: Vec<u32>,
    ccnt: Vec<u32>,
    cstart: Vec<u32>,
    ccur: Vec<u32>,
    sck: Vec<Ck>,
}
fn sort_ts<T: Copy>(v: &mut [T], f: impl Fn(&T) -> i64 + Copy) {
    if v.len() <= 24 {
        for i in 1..v.len() {
            let x = v[i];
            let kx = f(&x);
            let mut j = i;
            while j > 0 && f(&v[j - 1]) > kx {
                v[j] = v[j - 1];
                j -= 1;
            }
            v[j] = x;
        }
    } else {
        v.sort_unstable_by_key(|x| f(x));
    }
}
#[derive(Default)]
struct P3 {
    g: Grp,
    ev: Vec<Pe>,
    ck: Vec<Ck>,
    u_name: Vec<u64>,
    u_day: Vec<i32>,
    u_sess: Vec<i32>,
    u_ev: Vec<i32>,
    u_rev: Vec<i64>,
    u_top: Vec<u8>,
    acc: Vec<[u64; 4]>,
    cnt: Vec<u32>,
    pos: Vec<u32>,
    active: Vec<u32>,
}

fn main() {
    let t0 = Instant::now();
    let env = |k: &str, d: &str| std::env::var(k).unwrap_or(d.to_string());
    let data = PathBuf::from(env("DATA_DIR", "/data"));
    let outd = PathBuf::from(env("OUTPUT_DIR", "/output"));
    let nt: usize = env("NCPU", "0")
        .parse()
        .ok()
        .filter(|&n: &usize| n > 0)
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(8, |n| n.get()));
    // Ask the kernel to start reading every input file right away (async, deep queue);
    // events largest-first, which is the order the chunk tasks consume them.
    {
        let mut files: Vec<(u64, PathBuf)> = vec![];
        for sub in ["events", "clicks", "links"] {
            for p in list_csv(&data.join(sub)) {
                let sz = std::fs::metadata(&p).map_or(0, |m| m.len());
                files.push((if sub == "events" { u64::MAX / 2 + sz } else if sub == "clicks" { u64::MAX / 4 + sz } else { sz }, p));
            }
        }
        files.sort_by_key(|f| std::cmp::Reverse(f.0));
        std::thread::spawn(move || {
            use std::os::unix::io::AsRawFd;
            for (_, p) in files {
                if let Ok(f) = std::fs::File::open(&p) {
                    // SAFETY: plain syscall on a valid, open file descriptor; offset/len 0 = whole file.
                    unsafe {
                        libc::posix_fadvise(f.as_raw_fd(), 0, 0, libc::POSIX_FADV_WILLNEED);
                    }
                }
            }
        });
    }
    let verbose = std::env::var("SS_VERBOSE").is_ok();
    let lap = |s: &str| {
        if verbose {
            let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
            unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut ru) };
            let f = |t: libc::timeval| t.tv_sec as f64 + t.tv_usec as f64 * 1e-6;
            eprintln!("[{:7.3}s wall  user {:6.3}  sys {:6.3}  minflt {}] {}", t0.elapsed().as_secs_f64(), f(ru.ru_utime), f(ru.ru_stime), ru.ru_minflt, s);
        }
    };

    let manifest = String::from_utf8_lossy(read_small(&data.join("manifest.json"))).to_string();
    let ws = parse_ts(json_str(&manifest, "window_start").as_bytes()).unwrap();
    let we = parse_ts(json_str(&manifest, "window_end").as_bytes()).unwrap();

    // products / categories
    let prod = read_small(&data.join("products.csv"));
    let mut pl: Vec<(B, B)> = vec![];
    let mut first = true;
    for_lines(prod, |l| {
        if first {
            first = false;
            return;
        }
        if let Some([a, b]) = split::<2>(l) {
            pl.push((a, b));
        }
    });
    let mut catnames: Vec<B> = pl.iter().map(|x| x.1).collect();
    catnames.push(b"unknown");
    catnames.sort();
    catnames.dedup();
    assert!(catnames.len() <= 64);
    let unknown_cat = catnames.iter().position(|&c| c == b"unknown").unwrap() as u8;
    let mut products = Small { m: HM::default(), names: vec![] };
    let mut pcat: Vec<u8> = vec![];
    for (a, c) in &pl {
        products.m.insert(hash(a), products.names.len() as u32);
        products.names.push(a);
        pcat.push(catnames.iter().position(|x| x == c).unwrap() as u8);
    }
    // campaigns
    let camp = read_small(&data.join("campaigns.csv"));
    let mut campaigns = Small { m: HM::default(), names: vec![] };
    let mut channels: Vec<B> = vec![];
    first = true;
    for_lines(camp, |l| {
        if first {
            first = false;
            return;
        }
        if let Some([a, b]) = split::<2>(l) {
            campaigns.m.insert(hash(a), campaigns.names.len() as u32);
            campaigns.names.push(a);
            channels.push(b);
        }
    });
    let ncamp = campaigns.names.len();

    let load = |sub: &str| -> Vec<B> { list_csv(&data.join(sub)).iter().map(|p| map_file(p)).collect() };
    let ev_files = load("events");
    let ck_files = load("clicks");
    let lk_files = load("links");
    lap("mapped");
    if let Ok(mode) = std::env::var("SS_MODE") {
        let ech = chunks(&ev_files, 2 << 20);
        let mut sc = Scratch::default();
        let mut dc = DateCache::new();
        let mut bufs: Vec<Blocks<Ev1>> = new_blocks(EV_BLK);
        let mut one: Vec<Ev1> = Vec::with_capacity(2_300_000);
        let mut bufs2: Vec<Vec<Ev1>> = (0..NP).map(|_| Vec::with_capacity(20_000)).collect();
        let t = Instant::now();
        let mut cnt = 0u64;
        let mut chk = 0u64;
        for &(fi, s, e) in &ech {
            let d = &ev_files[fi][s..e];
            if std::env::var("SS_POP").is_ok() {
                populate(d);
            }
            match mode.as_str() {
                "memchr" => {
                    for_lines(d, |l| {
                        cnt += 1;
                        chk += l.len() as u64;
                    });
                }
                "scan" => {
                    scan(d, &mut sc);
                    cnt += sc.nl.len() as u64;
                }
                "lines" => lines::<7>(d, &mut sc, |f| {
                    cnt += 1;
                    chk += f[0].len() as u64;
                }),
                "hash" => lines::<7>(d, &mut sc, |f| {
                    cnt += 1;
                    chk += hash(f[0]) ^ hash(f[1]);
                }),
                "ts" => lines::<7>(d, &mut sc, |f| {
                    cnt += 1;
                    chk += parse_ts(f[2]).unwrap_or(0) as u64 ^ parse_ts(f[3]).unwrap_or(0) as u64;
                }),
                "p1np" => lines::<7>(d, &mut sc, |f| {
                    if let Some(ev) = make_ev(f, ws, we, &products, &pcat, unknown_cat, &mut dc) {
                        cnt += 1;
                        chk += ev.id ^ ev.user ^ ev.ts as u64;
                    }
                }),
                "p1one" => lines::<7>(d, &mut sc, |f| {
                    if let Some(ev) = make_ev(f, ws, we, &products, &pcat, unknown_cat, &mut dc) {
                        cnt += 1;
                        one.push(ev);
                    }
                }),
                "p1cap" => {
                    lines::<7>(d, &mut sc, |f| {
                        if let Some(ev) = make_ev(f, ws, we, &products, &pcat, unknown_cat, &mut dc) {
                            cnt += 1;
                            bufs[(ev.id >> 56) as usize].push(ev);
                        }
                    })
                }
                "p1twice" => {
                    // second pass reuses already-faulted memory: pure push cost
                    for b in bufs2.iter_mut() {
                        b.clear();
                    }
                    lines::<7>(d, &mut sc, |f| {
                        if let Some(ev) = make_ev(f, ws, we, &products, &pcat, unknown_cat, &mut dc) {
                            cnt += 1;
                            bufs2[(ev.id >> 56) as usize].push(ev);
                        }
                    })
                }
                "p1" => lines::<7>(d, &mut sc, |f| {
                    if let Some(ev) = make_ev(f, ws, we, &products, &pcat, unknown_cat, &mut dc) {
                        cnt += 1;
                        bufs[(ev.id >> 56) as usize].push(ev);
                    }
                }),
                _ => {}
            }
        }
        eprintln!("{mode}: {:.3}s for {cnt} lines ({:.1} ns/line) chk={chk}", t.elapsed().as_secs_f64(), t.elapsed().as_secs_f64() * 1e9 / cnt as f64);
        return;
    }


    let ech = chunks(&ev_files, 2 << 20);
    let ev_run = || -> Vec<Vec<Blocks<Ev1>>> { par(nt, ech.len(), || (Scratch::default(), new_blocks::<Ev1>(EV_BLK)), |st, t| {
        let (fi, s, e) = ech[t];
        populate(&ev_files[fi][s..e]);
        let (sc, st) = st;
        let mut dc = DateCache::new();
        lines::<7>(&ev_files[fi][s..e], sc, |f| {
            if let Some(ev) = make_ev(f, ws, we, &products, &pcat, unknown_cat, &mut dc) {
                st[(ev.id >> 56) as usize].push(ev);
            }
        });
    }).into_iter().map(|x| x.1).collect() };
    let (links, evs) = std::thread::scope(|s| {
        let h = s.spawn(|| build_links(&lk_files, 2));
        let evs = ev_run();
        (h.join().unwrap(), evs)
    });
    lap("links + events parsed");

    // clicks
    let cch = chunks(&ck_files, 4 << 20);
    let cks: Vec<Vec<Blocks<Ck>>> = par(nt, cch.len(), || (Scratch::default(), new_blocks::<Ck>(PE_BLK), Vec::<(u64, i64, u64, u32)>::new()), |st, t| {
        let (fi, s, e) = cch[t];
        populate(&ck_files[fi][s..e]);
        let (sc, st, tmp) = st;
        let mut dc = DateCache::new();
        tmp.clear();
        lines::<4>(&ck_files[fi][s..e], sc, |[cid, user, cmp, ts]| {
            if cid.is_empty() || user.is_empty() {
                return;
            }
            let Some(ts) = parse_ts_c(ts, &mut dc) else { return };
            if ts < ws - WEEK || ts >= we {
                return;
            }
            let Some(c) = campaigns.get(cmp) else { return };
            tmp.push((hash(user), ts, pack(cid), c));
        });
        // resolve person keys with lookahead prefetch (the link table is large)
        const LA: usize = 8;
        for i in 0..tmp.len() {
            if i + LA < tmp.len() {
                links.prefetch(tmp[i + LA].0);
            }
            let (uh, ts, cid, c) = tmp[i];
            let key = links.get(uh).map_or(uh, |v| v[0]);
            st[(key >> 56) as usize].push(Ck { key, ts, cid, camp: c });
        }
    }).into_iter().map(|x| x.1).collect();
    lap("clicks parsed");


    // pass 2: dedup, validate, person-map, scatter by person
    let pes: Vec<Vec<Blocks<Pe>>> = par(nt, NP, || S2 { out: new_blocks::<Pe>(PE_BLK), v: Vec::new(), tab: Vec::new(), surv: Vec::new() }, |s2, p| {
        let S2 { out: st, v, tab, surv } = s2;
        let n: usize = evs.iter().map(|t| t[p].len()).sum();
        v.clear();
        v.reserve(n);
        for t in &evs {
            for s in t[p].slices() {
                v.extend_from_slice(s);
            }
        }
        let cap = (v.len() * 2 + 2).next_power_of_two();
        let mask = cap - 1;
        tab.clear();
        tab.resize(cap, u64::MAX);
        for i in 0..v.len() {
            let id = v[i].id;
            let tag = (id >> 32) & 0xFFFF_FFFF;
            let mut s = ((id >> 8) as usize) & mask;
            loop {
                let e = tab[s];
                if e == u64::MAX {
                    tab[s] = (tag << 32) | i as u64;
                    break;
                }
                if e >> 32 == tag {
                    let j = (e & 0xFFFF_FFFF) as usize;
                    if v[j].id == id {
                        // duplicate event_id: the smaller ingest_ts copy survives (even if invalid)
                        if v[i].ing < v[j].ing {
                            v[j].valid = false;
                            tab[s] = (tag << 32) | i as u64;
                        } else {
                            v[i].valid = false;
                        }
                        break;
                    }
                }
                s = (s + 1) & mask;
            }
        }
        surv.clear();
        for (i, r) in v.iter().enumerate() {
            if r.valid {
                surv.push(i as u32);
            }
        }
        const LA: usize = 8;
        for k in 0..surv.len() {
            if k + LA < surv.len() {
                links.prefetch(v[surv[k + LA] as usize].user);
            }
            let r = v[surv[k] as usize];
            let (key, name) = match links.get(r.user) {
                Some(x) => (x[0], x[1]),
                None => (r.user, r.uptr),
            };
            st[(key >> 56) as usize].push(Pe { key, ts: r.ts, name, price: r.price, cat: r.cat, kind: r.kind });
        }
    }).into_iter().map(|s| s.out).collect();
    std::mem::forget(evs);
    lap("dedup");

    // pass 3
    let day0 = ws.div_euclid(DAY);
    let nd = ((we - 1).div_euclid(DAY) - day0 + 1) as usize;
    let organic = ncamp;
    std::fs::create_dir_all(outd.join("user_daily")).unwrap();
    std::fs::create_dir_all(outd.join("campaign_daily")).unwrap();
    let udir = outd.join("user_daily");
    let ud_specs = [
        pq::Spec { name: "user_id", kind: pq::Kind::Str, optional: false },
        pq::Spec { name: "day", kind: pq::Kind::Date, optional: false },
        pq::Spec { name: "sessions", kind: pq::Kind::I32, optional: false },
        pq::Spec { name: "events", kind: pq::Kind::I32, optional: false },
        pq::Spec { name: "revenue_cents", kind: pq::Kind::I64, optional: false },
        pq::Spec { name: "top_category", kind: pq::Kind::Str, optional: true },
    ];
    let ncat = catnames.len();
    // persons with clicks x events above this use the interval-sweep assist path (SS_SWEEP_MIN=0 forces it, for testing)
    let sweep_min: usize = std::env::var("SS_SWEEP_MIN").ok().and_then(|v| v.parse().ok()).unwrap_or(20_000);
    // heaviest partitions first (whales), so no big task is left for the tail
    let mut order3: Vec<usize> = (0..NP).collect();
    order3.sort_by_key(|&p| std::cmp::Reverse(pes.iter().map(|t| t[p].len()).sum::<usize>() + cks.iter().map(|t| t[p].len()).sum::<usize>()));
    let p3s: Vec<P3> = par(nt, NP, || P3 {
        acc: vec![[0; 4]; (ncamp + 1) * nd],
        cnt: vec![0; ncamp + 1],
        pos: vec![0; ncamp + 1],
        ..Default::default()
    }, |st, t_idx| {
        let p = order3[t_idx];
        let mut ev = std::mem::take(&mut st.ev);
        ev.clear();
        ev.reserve(pes.iter().map(|t| t[p].len()).sum());
        for t in &pes {
            for s in t[p].slices() {
                ev.extend_from_slice(s);
            }
        }
        let mut ck = std::mem::take(&mut st.ck);
        ck.clear();
        ck.reserve(cks.iter().map(|t| t[p].len()).sum());
        for t in &cks {
            for s in t[p].slices() {
                ck.extend_from_slice(s);
            }
        }
        let tp0 = Instant::now();
        let mut g = std::mem::take(&mut st.g);
        // group events by person with a hash table (O(n)), clicks join the same groups
        let n = ev.len();
        let cap = (n * 2 + 2).next_power_of_two();
        let mask = cap - 1;
        g.tkey.clear();
        g.tkey.resize(cap, 0);
        g.tgid.clear();
        g.tgid.resize(cap, 0);
        g.evg.clear();
        g.cnt.clear();
        for r in ev.iter() {
            let mut s = (r.key as usize) & mask;
            let gi = loop {
                let k = g.tkey[s];
                if k == r.key {
                    break g.tgid[s];
                }
                if k == 0 {
                    let id = g.cnt.len() as u32;
                    g.tkey[s] = r.key;
                    g.tgid[s] = id;
                    g.cnt.push(0);
                    break id;
                }
                s = (s + 1) & mask;
            };
            g.evg.push(gi);
            g.cnt[gi as usize] += 1;
        }
        let ng = g.cnt.len();
        g.start.clear();
        let mut run = 0u32;
        for &c in g.cnt.iter() {
            g.start.push(run);
            run += c;
        }
        g.start.push(run);
        g.cur.clear();
        g.cur.extend_from_slice(&g.start[..ng]);
        g.sev.clear();
        g.sev.resize(n, Pe { key: 0, ts: 0, name: 0, price: 0, cat: 0, kind: 0 });
        for (i, r) in ev.iter().enumerate() {
            let gi = g.evg[i] as usize;
            let p = g.cur[gi] as usize;
            g.sev[p] = *r;
            g.cur[gi] += 1;
        }
        g.ccnt.clear();
        g.ccnt.resize(ng, 0);
        g.cgid.clear();
        for c in ck.iter() {
            let mut s = (c.key as usize) & mask;
            let gi = loop {
                let k = g.tkey[s];
                if k == c.key {
                    break g.tgid[s];
                }
                if k == 0 {
                    break u32::MAX;
                }
                s = (s + 1) & mask;
            };
            g.cgid.push(gi);
            if gi != u32::MAX {
                g.ccnt[gi as usize] += 1;
            }
        }
        g.cstart.clear();
        let mut run = 0u32;
        for &c in g.ccnt.iter() {
            g.cstart.push(run);
            run += c;
        }
        g.cstart.push(run);
        g.ccur.clear();
        g.ccur.extend_from_slice(&g.cstart[..ng]);
        g.sck.clear();
        g.sck.resize(run as usize, Ck { key: 0, ts: 0, cid: 0, camp: 0 });
        for (i, c) in ck.iter().enumerate() {
            let gi = g.cgid[i];
            if gi != u32::MAX {
                let p = g.ccur[gi as usize] as usize;
                g.sck[p] = *c;
                g.ccur[gi as usize] += 1;
            }
        }
        let mut u_name = std::mem::take(&mut st.u_name);
        let mut u_day = std::mem::take(&mut st.u_day);
        let mut u_sess = std::mem::take(&mut st.u_sess);
        let mut u_ev = std::mem::take(&mut st.u_ev);
        let mut u_rev = std::mem::take(&mut st.u_rev);
        let mut u_top = std::mem::take(&mut st.u_top);
        let tp1 = tp0.elapsed();
        let mut t_sort = std::time::Duration::ZERO;
        for gi in 0..ng {
            let (a, b) = (g.start[gi] as usize, g.start[gi + 1] as usize);
            let (ca, cb) = (g.cstart[gi] as usize, g.cstart[gi + 1] as usize);
            let ts0 = Instant::now();
            sort_ts(&mut g.sev[a..b], |r: &Pe| r.ts);
            sort_ts(&mut g.sck[ca..cb], |c: &Ck| c.ts);
            t_sort += ts0.elapsed();
            let es = &g.sev[a..b];
            let cs = &g.sck[ca..cb];
            let _t_person = WhaleTimer(if es.len() > 3000 && std::env::var("SS_WHALE").is_ok() { Some(Instant::now()) } else { None }, es.len(), cs.len());
            let name = es[0].name;
            let (mut lo, mut hi) = (0usize, 0usize);
            let mut in_sess = false;
            let mut last = 0i64;
            let mut cur_day = i64::MIN;
            let (mut ud_s, mut ud_e, mut ud_r) = (0i32, 0i32, 0i64);
            let mut cats = [0u64; 64];
            let mut s_camp = 0usize;
            let mut s_d = 0usize;
            let mut s_purch = false;
            // Heavy persons (many clicks and sessions): compute assists by interval sweep afterwards
            // instead of walking every active campaign for every session.
            let sweep = !cs.is_empty() && cs.len() * es.len() >= sweep_min;
            let mut sw_start: Vec<i64> = Vec::new();
            let mut sw_day: Vec<u32> = Vec::new();
            macro_rules! flush {
                () => {
                    if cur_day != i64::MIN {
                        u_name.push(name);
                        u_day.push(cur_day as i32);
                        u_sess.push(ud_s);
                        u_ev.push(ud_e);
                        u_rev.push(ud_r);
                        if ud_r > 0 {
                            let mut b = 0usize;
                            for c in 1..ncat {
                                if cats[c] > cats[b] {
                                    b = c;
                                }
                            }
                            u_top.push(b as u8);
                        } else {
                            u_top.push(255);
                        }
                        cats[..ncat].fill(0);
                    }
                };
            }
            for r in es {
                if !in_sess || r.ts - last > GAP {
                    let start = r.ts;
                    let day = start.div_euclid(DAY);
                    if day != cur_day {
                        flush!();
                        cur_day = day;
                        ud_s = 0;
                        ud_e = 0;
                        ud_r = 0;
                    }
                    ud_s += 1;
                    while hi < cs.len() && cs[hi].ts <= start {
                        if !sweep {
                            let c = cs[hi].camp as usize;
                            if st.cnt[c] == 0 {
                                st.pos[c] = st.active.len() as u32;
                                st.active.push(c as u32);
                            }
                            st.cnt[c] += 1;
                        }
                        hi += 1;
                    }
                    while lo < hi && cs[lo].ts < start - WEEK {
                        if !sweep {
                            let c = cs[lo].camp as usize;
                            st.cnt[c] -= 1;
                            if st.cnt[c] == 0 {
                                let pi = st.pos[c] as usize;
                                let lastc = *st.active.last().unwrap();
                                st.active.swap_remove(pi);
                                if pi < st.active.len() {
                                    st.pos[lastc as usize] = pi as u32;
                                }
                            }
                        }
                        lo += 1;
                    }
                    s_d = (day - day0) as usize;
                    s_camp = organic;
                    if hi > lo {
                        let t = cs[hi - 1].ts;
                        let mut best = hi - 1;
                        let mut j = hi - 1;
                        while j > lo {
                            j -= 1;
                            if cs[j].ts != t {
                                break;
                            }
                            if unpack(cs[j].cid) < unpack(cs[best].cid) {
                                best = j;
                            }
                        }
                        s_camp = cs[best].camp as usize;
                    }
                    if sweep {
                        sw_start.push(start);
                        sw_day.push(s_d as u32);
                    } else {
                        for &c in &st.active {
                            st.acc[c as usize * nd + s_d][3] += 1;
                        }
                    }
                    st.acc[s_camp * nd + s_d][0] += 1;
                    in_sess = true;
                    s_purch = false;
                }
                last = r.ts;
                ud_e += 1;
                if r.kind == 2 {
                    let p = r.price as u64;
                    ud_r += p as i64;
                    cats[r.cat as usize] += p;
                    let a = &mut st.acc[s_camp * nd + s_d];
                    a[2] += p;
                    if !s_purch {
                        s_purch = true;
                        a[1] += 1;
                    }
                }
            }
            flush!();
            if sweep {
                let ns = sw_start.len();
                let mut day_first = vec![ns as u32; nd + 1];
                let mut d_next = 0usize;
                for (i, &d) in sw_day.iter().enumerate() {
                    while d_next <= d as usize {
                        day_first[d_next] = i as u32;
                        d_next += 1;
                    }
                }
                let mut pairs: Vec<(u32, i64)> = cs.iter().map(|c| (c.camp, c.ts)).collect();
                pairs.sort_unstable();
                let mut k = 0;
                while k < pairs.len() {
                    let c = pairs[k].0 as usize;
                    let (mut a, mut b) = (pairs[k].1, pairs[k].1 + WEEK);
                    let mut j = k + 1;
                    loop {
                        let at_end = j >= pairs.len() || pairs[j].0 as usize != c;
                        if at_end || pairs[j].1 > b {
                            add_interval(&mut st.acc, nd, &sw_start, &sw_day, &day_first, c, a, b);
                            if at_end {
                                break;
                            }
                            a = pairs[j].1;
                            b = a + WEEK;
                        } else {
                            b = pairs[j].1 + WEEK;
                        }
                        j += 1;
                    }
                    k = j;
                }
            } else {
                for j in lo..hi {
                    let c = cs[j].camp as usize;
                    st.cnt[c] -= 1;
                    if st.cnt[c] == 0 {
                        let pi = st.pos[c] as usize;
                        let lastc = *st.active.last().unwrap();
                        st.active.swap_remove(pi);
                        if pi < st.active.len() {
                            st.pos[lastc as usize] = pi as u32;
                        }
                    }
                }
            }
        }
        if std::env::var("SS_TASKS").is_ok() && tp0.elapsed().as_millis() > 25 {
            eprintln!("  p3 task {}: {} ev {} ck {} groups: build {:.1}ms sort {:.1}ms total {:.1}ms", p, n, ck.len(), ng, tp1.as_secs_f64() * 1e3, t_sort.as_secs_f64() * 1e3, tp0.elapsed().as_secs_f64() * 1e3);
        }
        if u_name.len() >= FLUSH_ROWS {
            flush_users(&udir, &ud_specs, &catnames, &u_name, &u_day, &u_sess, &u_ev, &u_rev, &u_top);
            u_name.clear();
            u_day.clear();
            u_sess.clear();
            u_ev.clear();
            u_rev.clear();
            u_top.clear();
        }
        st.ev = ev;
        st.ck = ck;
        st.g = g;
        st.u_name = u_name;
        st.u_day = u_day;
        st.u_sess = u_sess;
        st.u_ev = u_ev;
        st.u_rev = u_rev;
        st.u_top = u_top;
    });
    // leftover rows of each worker state (< FLUSH_ROWS each), written in parallel
    par(nt, p3s.len(), || (), |_, t| {
        let s = &p3s[t];
        if !s.u_name.is_empty() {
            flush_users(&udir, &ud_specs, &catnames, &s.u_name, &s.u_day, &s.u_sess, &s.u_ev, &s.u_rev, &s.u_top);
        }
    });
    if FILE_ID.load(Ordering::Relaxed) == 0 {
        flush_users(&udir, &ud_specs, &catnames, &[], &[], &[], &[], &[], &[]);
    }
    lap("sessions + user_daily");

    // campaign_daily
    let mut tot = vec![[0u64; 4]; (ncamp + 1) * nd];
    for s in &p3s {
        for (a, b) in tot.iter_mut().zip(&s.acc) {
            for k in 0..4 {
                a[k] += b[k];
            }
        }
    }
    let (mut c_id, mut c_ch, mut c_day) = (vec![], vec![], vec![]);
    let (mut c_s, mut c_p, mut c_r, mut c_a) = (vec![], vec![], vec![], vec![]);
    for c in 0..=ncamp {
        for d in 0..nd {
            let a = tot[c * nd + d];
            if a[0] > 0 || a[3] > 0 {
                let (id, ch): (B, B) = if c == ncamp { (b"organic", b"organic") } else { (campaigns.names[c], channels[c]) };
                c_id.push(id);
                c_ch.push(ch);
                c_day.push((day0 + d as i64) as i32);
                c_s.push(a[0] as i32);
                c_p.push(a[1] as i32);
                c_r.push(a[2] as i64);
                c_a.push(a[3] as i32);
            }
        }
    }
    let specs = [
        pq::Spec { name: "campaign_id", kind: pq::Kind::Str, optional: false },
        pq::Spec { name: "channel", kind: pq::Kind::Str, optional: false },
        pq::Spec { name: "day", kind: pq::Kind::Date, optional: false },
        pq::Spec { name: "sessions", kind: pq::Kind::I32, optional: false },
        pq::Spec { name: "purchasing_sessions", kind: pq::Kind::I32, optional: false },
        pq::Spec { name: "revenue_cents", kind: pq::Kind::I64, optional: false },
        pq::Spec { name: "assisted_sessions", kind: pq::Kind::I32, optional: false },
    ];
    let n = c_id.len();
    let pages = [
        pq::str_page(c_id.iter().copied(), n),
        pq::str_page(c_ch.iter().copied(), n),
        pq::i32_page(&c_day),
        pq::i32_page(&c_s),
        pq::i32_page(&c_p),
        pq::i64_page(&c_r),
        pq::i32_page(&c_a),
    ];
    write_file(&outd.join("campaign_daily"), "part-0.parquet", pq::file_bytes(&specs, &pages, n));
    lap("done");
    std::process::exit(0);
}

#[cfg(test)]
mod tests {
    use super::*;

    const T: i64 = 1_791_071_890_000; // 2026-10-03T23:58:10Z

    #[test]
    fn timestamp_forms() {
        assert_eq!(parse_ts(b"2026-10-03T23:58:10Z"), Some(T));
        assert_eq!(parse_ts(b"2026-10-03T19:58:10-04:00"), Some(T));
        assert_eq!(parse_ts(b"2026-10-04T05:58:10+06:00"), Some(T));
        assert_eq!(parse_ts(b"2026-10-03T23:58:10-00:00"), Some(T));
        assert_eq!(parse_ts(b"1791071890000"), Some(T));
        assert_eq!(parse_ts(b"0001791071890000"), Some(T));
        assert_eq!(parse_ts(b"86400000"), Some(86_400_000));
    }

    #[test]
    fn timestamp_rejects() {
        for bad in [
            &b""[..],
            b"2026-10-03T23:58:10.5Z",
            b"2026-10-03t23:58:10Z",
            b"2026-10-03 23:58:10Z",
            b"2026-10-03T23:58:10",
            b"2026-13-03T23:58:10Z",
            b"2026-02-30T23:58:10Z",
            b"2027-02-29T23:58:10Z",
            b"2026-10-03T24:00:00Z",
            b"2026-10-03T23:58:60Z",
            b"2026-10-03T23:58:10+24:00",
            b"2026-10-03T23:58:10+05:60",
            b"2026-10-03T23:58:10+0200",
            b"1791071890000.0",
            b"1.79e12",
            b"-5",
            b"99999999999999999999999",
        ] {
            assert_eq!(parse_ts(bad), None, "{}", String::from_utf8_lossy(bad));
        }
        assert_eq!(parse_ts(b"2028-02-29T00:00:00Z"), Some(1_835_395_200_000));
    }

    #[test]
    fn date_cache_matches_uncached() {
        let mut dc = DateCache::new();
        for _ in 0..3 {
            assert_eq!(parse_ts_c(b"2026-10-03T23:58:10Z", &mut dc), Some(T));
            assert_eq!(parse_ts_c(b"2026-10-04T05:58:10+06:00", &mut dc), Some(T));
            assert_eq!(parse_ts_c(b"2026-02-30T00:00:00Z", &mut dc), None);
        }
    }

    #[test]
    fn csv_lines_and_quotes() {
        let d: B = b"a,b\n1,\"x\"\n\"1\",\"\"\n1,2,3\n\n\"u,2\n1,\"a\"b\n3,4\n5,6";
        let mut sc = Scratch::default();
        let mut got: Vec<(Vec<u8>, Vec<u8>)> = vec![];
        // header already skipped by callers; here the first line "a,b" is just data
        lines::<2>(d, &mut sc, |[x, y]| got.push((x.to_vec(), y.to_vec())));
        let want: Vec<(&[u8], &[u8])> = vec![(b"a", b"b"), (b"1", b"x"), (b"1", b""), (b"3", b"4"), (b"5", b"6")];
        assert_eq!(got.len(), want.len());
        for (g, w) in got.iter().zip(want) {
            assert_eq!((&g.0[..], &g.1[..]), w);
        }
    }

    #[test]
    fn hash_is_nonzero_and_distinguishes() {
        assert_ne!(hash(b""), 0);
        assert_ne!(hash(b"u1"), hash(b"U1"));
        assert_ne!(hash(b"u1"), hash(b"u1 "));
        assert_eq!(hash(b"abcdefghij"), hash(b"abcdefghij"));
    }
}
