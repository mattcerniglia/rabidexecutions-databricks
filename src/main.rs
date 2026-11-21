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
    let mut s = P0 ^ (b.len() as u64).wrapping_mul(P2);
    let mut i = 0;
    while i + 8 <= b.len() {
        let w = u64::from_le_bytes(b[i..i + 8].try_into().unwrap());
        s = mix(s ^ w, P1);
        i += 8;
    }
    if i < b.len() {
        let mut w = 0u64;
        for (j, &c) in b[i..].iter().enumerate() {
            w |= (c as u64) << (8 * j);
        }
        s = mix(s ^ w ^ 0x1000, P2);
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
fn parse_ts(f: &[u8]) -> Option<i64> {
    let l = f.len();
    if (l == 20 && f[19] == b'Z') || (l == 25 && (f[19] == b'+' || f[19] == b'-')) {
        let y = d2(&f[0..2])? * 100 + d2(&f[2..4])?;
        if f[4] != b'-' || f[7] != b'-' || f[10] != b'T' || f[13] != b':' || f[16] != b':' {
            return None;
        }
        let mo = d2(&f[5..7])?;
        let d = d2(&f[8..10])?;
        let hh = d2(&f[11..13])?;
        let mi = d2(&f[14..16])?;
        let ss = d2(&f[17..19])?;
        if !(1..=12).contains(&mo) || d < 1 || hh > 23 || mi > 59 || ss > 59 {
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
        let mut t = (days_from_civil(y, mo, d) * 86400 + hh * 3600 + mi * 60 + ss) * 1000;
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

fn par<S: Send>(nt: usize, ntasks: usize, init: impl Fn() -> S + Sync, f: impl Fn(&mut S, usize) + Sync) -> Vec<S> {
    let ctr = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        let hs: Vec<_> = (0..nt)
            .map(|_| {
                sc.spawn(|| {
                    let mut s = init();
                    loop {
                        let t = ctr.fetch_add(1, Ordering::Relaxed);
                        if t >= ntasks {
                            break;
                        }
                        f(&mut s, t);
                    }
                    s
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    })
}

// ---------- link table ----------
struct LinkTab {
    mask: usize,
    keys: Vec<u64>,
    vals: Vec<[u64; 2]>, // person key, name ptr
}
impl LinkTab {
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
    let res = par(nt, ch.len(), Vec::<(B, B)>::new, |st, t| {
        let (fi, s, e) = ch[t];
        for_lines(&files[fi][s..e], |l| {
            if let Some([a, b]) = split::<2>(l) {
                if !a.is_empty() && !b.is_empty() {
                    st.push((a, b));
                }
            }
        });
    });
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

struct P3 {
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
    let verbose = std::env::var("SS_VERBOSE").is_ok();
    let lap = |s: &str| {
        if verbose {
            let mut ts = libc::timespec { tv_sec: 0, tv_nsec: 0 };
            unsafe { libc::clock_gettime(libc::CLOCK_PROCESS_CPUTIME_ID, &mut ts) };
            eprintln!("[{:7.3}s wall {:7.3}s cpu] {}", t0.elapsed().as_secs_f64(), ts.tv_sec as f64 + ts.tv_nsec as f64 * 1e-9, s);
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

    let links = build_links(&lk_files, nt);
    lap("links");

    // clicks
    let cch = chunks(&ck_files, 4 << 20);
    let cks: Vec<Vec<Vec<Ck>>> = par(nt, cch.len(), || (0..NP).map(|_| Vec::new()).collect::<Vec<Vec<Ck>>>(), |st, t| {
        let (fi, s, e) = cch[t];
        for_lines(&ck_files[fi][s..e], |l| {
            let Some([cid, user, cmp, ts]) = split::<4>(l) else { return };
            if cid.is_empty() || user.is_empty() {
                return;
            }
            let Some(ts) = parse_ts(ts) else { return };
            if ts < ws - WEEK || ts >= we {
                return;
            }
            let Some(c) = campaigns.get(cmp) else { return };
            let uh = hash(user);
            let key = links.get(uh).map_or(uh, |v| v[0]);
            st[(key >> 56) as usize].push(Ck { key, ts, cid: pack(cid), camp: c });
        });
    });
    lap("clicks parsed");

    // events pass 1
    let ech = chunks(&ev_files, 4 << 20);
    let evs: Vec<Vec<Vec<Ev1>>> = par(nt, ech.len(), || (0..NP).map(|_| Vec::new()).collect::<Vec<Vec<Ev1>>>(), |st, t| {
        let (fi, s, e) = ech[t];
        for_lines(&ev_files[fi][s..e], |l| {
            let Some([id, user, ts, ing, ty, pr, price]) = split::<7>(l) else { return };
            if id.is_empty() {
                return;
            }
            let ing = parse_ts(ing).unwrap_or(i64::MAX);
            let tsv = parse_ts(ts);
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
            let idh = hash(id);
            st[(idh >> 56) as usize].push(Ev1 { id: idh, user: hash(user), ts: tsx, ing, uptr: pack(user), price: pv, cat, kind, valid });
        });
    });
    lap("events parsed");

    // pass 2: dedup, validate, person-map, scatter by person
    let pes: Vec<Vec<Vec<Pe>>> = par(nt, NP, || (0..NP).map(|_| Vec::new()).collect::<Vec<Vec<Pe>>>(), |st, p| {
        let n: usize = evs.iter().map(|t| t[p].len()).sum();
        let mut v: Vec<Ev1> = Vec::with_capacity(n);
        for t in &evs {
            v.extend_from_slice(&t[p]);
        }
        let cap = (v.len() * 2 + 2).next_power_of_two();
        let mask = cap - 1;
        let mut tab = vec![u32::MAX; cap];
        for i in 0..v.len() {
            let id = v[i].id;
            let mut s = ((id >> 8) as usize) & mask;
            loop {
                let j = tab[s];
                if j == u32::MAX {
                    tab[s] = i as u32;
                    break;
                }
                let o = &v[j as usize];
                if o.id == id {
                    if v[i].ing < o.ing {
                        tab[s] = i as u32;
                    }
                    break;
                }
                s = (s + 1) & mask;
            }
        }
        for &j in &tab {
            if j == u32::MAX {
                continue;
            }
            let r = v[j as usize];
            if !r.valid {
                continue;
            }
            let (key, name) = match links.get(r.user) {
                Some(x) => (x[0], x[1]),
                None => (r.user, r.uptr),
            };
            st[(key >> 56) as usize].push(Pe { key, ts: r.ts, name, price: r.price, cat: r.cat, kind: r.kind });
        }
    });
    drop(evs);
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
    let p3s: Vec<P3> = par(nt, NP, || P3 {
        acc: vec![[0; 4]; (ncamp + 1) * nd],
        cnt: vec![0; ncamp + 1],
        pos: vec![0; ncamp + 1],
        active: vec![],
    }, |st, p| {
        let mut ev: Vec<Pe> = Vec::with_capacity(pes.iter().map(|t| t[p].len()).sum());
        for t in &pes {
            ev.extend_from_slice(&t[p]);
        }
        let mut ck: Vec<Ck> = Vec::with_capacity(cks.iter().map(|t| t[p].len()).sum());
        for t in &cks {
            ck.extend_from_slice(&t[p]);
        }
        ev.sort_unstable_by(|a, b| a.key.cmp(&b.key).then(a.ts.cmp(&b.ts)));
        ck.sort_unstable_by(|a, b| a.key.cmp(&b.key).then(a.ts.cmp(&b.ts)));
        let mut u_name: Vec<u64> = vec![];
        let mut u_day: Vec<i32> = vec![];
        let mut u_sess: Vec<i32> = vec![];
        let mut u_ev: Vec<i32> = vec![];
        let mut u_rev: Vec<i64> = vec![];
        let mut u_top: Vec<u8> = vec![];
        let mut i = 0;
        let mut cj = 0;
        while i < ev.len() {
            let key = ev[i].key;
            let mut e = i;
            while e < ev.len() && ev[e].key == key {
                e += 1;
            }
            while cj < ck.len() && ck[cj].key < key {
                cj += 1;
            }
            let mut ce = cj;
            while ce < ck.len() && ck[ce].key == key {
                ce += 1;
            }
            let es = &ev[i..e];
            let cs = &ck[cj..ce];
            i = e;
            cj = ce;
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
                        let c = cs[hi].camp as usize;
                        if st.cnt[c] == 0 {
                            st.pos[c] = st.active.len() as u32;
                            st.active.push(c as u32);
                        }
                        st.cnt[c] += 1;
                        hi += 1;
                    }
                    while lo < hi && cs[lo].ts < start - WEEK {
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
                    for &c in &st.active {
                        st.acc[c as usize * nd + s_d][3] += 1;
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
        if !u_name.is_empty() || p == 0 {
            let n = u_name.len();
            let tops: Vec<Option<B>> = u_top.iter().map(|&t| if t == 255 { None } else { Some(catnames[t as usize]) }).collect();
            let pages = [
                pq::str_page(u_name.iter().map(|&p| unpack(p)), n),
                pq::i32_page(&u_day),
                pq::i32_page(&u_sess),
                pq::i32_page(&u_ev),
                pq::i64_page(&u_rev),
                pq::opt_str_page(&tops),
            ];
            write_file(&udir, &format!("part-{:03}.parquet", p), pq::file_bytes(&ud_specs, &pages, n));
        }
    });
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
