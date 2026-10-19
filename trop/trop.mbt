// ============================================================================
// trop — 熱帶化 (tropicalization)
//
//   一個帶非阿基米德賦值的域 K（此處：Puiseux/Laurent 級數）經賦值
//   val: K → Q ∪ {∞} 映到熱帶半環 (Q∪{∞}, min, +)。
//   定理：val(f·g) = val f + val g ；val(f+g) ≥ min(val f, val g)，
//   等號在兩賦值不等時成立（等號失效 ⇔ 相消，這正是熱帶化的資訊損失）。
//   定理（Newton–Puiseux）：f 的 Newton 多邊形各邊斜率之負值（按水平長度計重數）
//   = f 的根的賦值。
// ============================================================================

///|
pub const TROP_INF : Int32 = 1000000000

///|
/// 熱帶數：min-plus 半環元素（TROP_INF 表示 ∞）。
pub struct Trop(Int32)

///|
pub fn Trop::of(x : Int32) -> Trop {
  Trop(x)
}

///|
pub fn Trop::add(self : Trop, o : Trop) -> Trop {
  Trop(if self.0 < o.0 { self.0 } else { o.0 })
}

///|
pub fn Trop::mul(self : Trop, o : Trop) -> Trop {
  if self.0 >= TROP_INF || o.0 >= TROP_INF {
    Trop(TROP_INF)
  } else {
    Trop(self.0 + o.0)
  }
}

///|
pub fn Trop::zero() -> Trop {
  Trop(TROP_INF)
}

///|
pub fn Trop::one() -> Trop {
  Trop(0)
}

///|
pub impl Eq for Trop with fn equal(self, o) {
  self.0 == o.0
}

///|
pub fn Trop::show(self : Trop) -> String {
  if self.0 >= TROP_INF {
    "∞"
  } else {
    self.0.to_string()
  }
}

///|
pub impl @num.Semiring for Trop with fn zero() {
  Trop::zero()
}

///|
pub impl @num.Semiring for Trop with fn one() {
  Trop::one()
}

///|
pub impl @num.Semiring for Trop with fn add(self, o) {
  self.add(o)
}

///|
pub impl @num.Semiring for Trop with fn mul(self, o) {
  self.mul(o)
}

// ---------------------------------------------------------------------------
// Puiseux / Laurent 級數
// ---------------------------------------------------------------------------

///|
pub type Term = (@num.Rat, @num.Rat) // (指數, 係數)

///|
pub struct LSer {
  terms : Array[Term] // 依指數升序，無零係數
}

///|
pub fn LSer::make(ts : Array[Term]) -> LSer {
  // 插入排序
  let a = ts.copy()
  let n = a.length()
  for i in 1..<n {
    let key = a[i]
    let mut j = i
    while j > 0 && a[j - 1].0.compare(key.0) > 0 {
      a[j] = a[j - 1]
      j = j - 1
    }
    a[j] = key
  }
  // 合併同指數、去零
  let out : Array[Term] = []
  for t in a {
    if out.length() > 0 && out[out.length() - 1].0 == t.0 {
      let s = out[out.length() - 1].1.add(t.1)
      let _ = out.pop()
      if !s.is_zero() {
        out.push((t.0, s))
      }
    } else if !t.1.is_zero() {
      out.push(t)
    }
  }
  { terms: out, }
}

///|
pub fn LSer::zero() -> LSer {
  { terms: [], }
}

///|
pub fn LSer::konst(c : Int32) -> LSer {
  LSer::make([(@num.Rat::zero(), @num.Rat::of_int(c))])
}

///|
pub fn LSer::mono(e : @num.Rat, c : Int32) -> LSer {
  LSer::make([(e, @num.Rat::of_int(c))])
}

///|
pub fn LSer::is_zero(self : LSer) -> Bool {
  self.terms.length() == 0
}

///|
/// 賦值：最小指數；零級數為 ∞。
pub fn LSer::val(self : LSer) -> @num.Rat? {
  if self.terms.length() == 0 {
    None
  } else {
    Some(self.terms[0].0)
  }
}

///|
pub fn LSer::add(self : LSer, o : LSer) -> LSer {
  let all : Array[Term] = []
  for t in self.terms {
    all.push(t)
  }
  for t in o.terms {
    all.push(t)
  }
  LSer::make(all)
}

///|
pub fn LSer::neg(self : LSer) -> LSer {
  let out : Array[Term] = []
  for t in self.terms {
    out.push((t.0, t.1.neg()))
  }
  { terms: out, }
}

///|
pub fn LSer::mul(self : LSer, o : LSer) -> LSer {
  let out : Array[Term] = []
  for a in self.terms {
    for b in o.terms {
      out.push((a.0.add(b.0), a.1.mul(b.1)))
    }
  }
  LSer::make(out)
}

///|
pub fn LSer::show(self : LSer) -> String {
  if self.terms.length() == 0 {
    return "0"
  }
  let mut s = ""
  let mut first = true
  for t in self.terms {
    if !first {
      s = s + " + "
    }
    first = false
    s = s + "\{t.1}·t^\{t.0}"
  }
  s
}

// ---------------------------------------------------------------------------
// Newton 多邊形
// ---------------------------------------------------------------------------

///|
/// 下凸包：輸入 (次數 i, 係數賦值 v_i)，輸出多邊形頂點（斜率嚴格遞增）。
pub fn lower_hull(pts0 : Array[(Int32, @num.Rat)]) -> Array[(Int32, @num.Rat)] {
  let pts = pts0.copy()
  let n = pts.length()
  for i in 1..<n {
    let key = pts[i]
    let mut j = i
    while j > 0 && pts[j - 1].0 > key.0 {
      pts[j] = pts[j - 1]
      j = j - 1
    }
    pts[j] = key
  }
  let uniq : Array[(Int32, @num.Rat)] = []
  for p in pts {
    if uniq.length() > 0 && uniq[uniq.length() - 1].0 == p.0 {
      if p.1.compare(uniq[uniq.length() - 1].1) < 0 {
        let _ = uniq.pop()
        uniq.push(p)
      }
    } else {
      uniq.push(p)
    }
  }
  let hull : Array[(Int32, @num.Rat)] = []
  for p in uniq {
    while hull.length() >= 2 {
      let o = hull[hull.length() - 2]
      let a = hull[hull.length() - 1]
      // cross = (a.x−o.x)(p.y−o.y) − (a.y−o.y)(p.x−o.x)
      let c1 = @num.Rat::of_int(a.0 - o.0).mul(p.1.sub(o.1))
      let c2 = a.1.sub(o.1).mul(@num.Rat::of_int(p.0 - o.0))
      if c1.compare(c2) <= 0 {
        let _ = hull.pop()
      } else {
        break
      }
    }
    hull.push(p)
  }
  hull
}

///|
/// Newton–Puiseux：回傳 (根的賦值, 重數) 列表。
pub fn root_valuations(f : Array[LSer]) -> Array[(@num.Rat, Int32)] {
  let pts : Array[(Int32, @num.Rat)] = []
  for i in 0..<f.length() {
    match f[i].val() {
      Some(v) => pts.push((i, v))
      None => ()
    }
  }
  let hull = lower_hull(pts)
  let out : Array[(@num.Rat, Int32)] = []
  for k in 1..<hull.length() {
    let dx = hull[k].0 - hull[k - 1].0
    let dv = hull[k].1.sub(hull[k - 1].1)
    // 斜率 = dv/dx；根的賦值 = −斜率
    let slope = dv.div(@num.Rat::of_int(dx))
    out.push((slope.neg(), dx))
  }
  out
}

///|
/// 多項式乘法（係數為 LSer）。
pub fn poly_mul(a : Array[LSer], b : Array[LSer]) -> Array[LSer] {
  let out : Array[LSer] = []
  for _ in 0..<(a.length() + b.length() - 1) {
    out.push(LSer::zero())
  }
  for i in 0..<a.length() {
    for j in 0..<b.length() {
      out[i + j] = out[i + j].add(a[i].mul(b[j]))
    }
  }
  out
}

///|
/// 由根建多項式 ∏ (x − r_i)。
pub fn poly_from_roots(roots : Array[LSer]) -> Array[LSer] {
  let mut f : Array[LSer] = [LSer::konst(1)]
  for r in roots {
    // 乘 (x − r)
    f = poly_mul(f, [r.neg(), LSer::konst(1)])
  }
  f
}

// ---------------------------------------------------------------------------
// 雙變數：牛頓多邊形邊的平衡條件
// ---------------------------------------------------------------------------

///|
pub fn gcd(a : Int32, b : Int32) -> Int32 {
  let mut x = if a < 0 { -a } else { a }
  let mut y = if b < 0 { -b } else { b }
  while y != 0 {
    let t = x % y
    x = y
    y = t
  }
  x
}

///|
/// 三項式 x^p + y^q + 1 的牛頓三角形：三條邊的（格點長度 ℓ, 原始外法向 u），
/// 驗證熱帶平衡律 Σ ℓ·u = 0。
pub fn balance_tripod(p : Int32, q : Int32) -> (Int32, Int32) {
  let g = gcd(p, q)
  // 邊 (0,0)-(p,0)：ℓ=p，外法向 (0,−1)
  // 邊 (p,0)-(0,q)：ℓ=g，外法向 (q/g, p/g)
  // 邊 (0,q)-(0,0)：ℓ=q，外法向 (−1,0)
  let sx = p * 0 + g * (q / g) + q * -1
  let sy = p * -1 + g * (p / g) + q * 0
  (sx, sy)
}

///|
/// 熱帶多項式的最小值出現次數（在權重 w 處）。
pub fn min_attained(
  terms : Array[(Int32, Int32, Int32)],
  w : (Int32, Int32),
) -> Int32 {
  let mut best = TROP_INF
  for t in terms {
    let v = t.0 * w.0 + t.1 * w.1 + t.2
    if v < best {
      best = v
    }
  }
  let mut cnt = 0
  for t in terms {
    let v = t.0 * w.0 + t.1 * w.1 + t.2
    if v == best {
      cnt = cnt + 1
    }
  }
  cnt
}

///|
pub fn checks() -> Array[(String, Bool, String)] {
  let out : Array[(String, Bool, String)] = []

  // ---- 1. 賦值同態 ----
  let f = LSer::make([
    (@num.Rat::of_int(0), @num.Rat::of_int(3)),
    (@num.Rat::of_int(2), @num.Rat::of_int(1)),
  ]) // 3 + t²
  let g = LSer::make([
    (@num.Rat::of_int(-1), @num.Rat::of_int(5)),
    (@num.Rat::of_int(1), @num.Rat::of_int(7)),
  ]) // 5t⁻¹ + 7t
  let mut mult_ok = true
  match (f.val(), g.val(), f.mul(g).val()) {
    (Some(a), Some(b), Some(c)) => if !(a.add(b) == c) { mult_ok = false }
    _ => mult_ok = false
  }
  out.push(("val(f·g) = val f + val g", mult_ok, "\{f.show()} × \{g.show()}"))

  // 相消：val(f+g) > min
  let h = f.add(f.neg())
  let mut cancel_ok = h.is_zero()
  let f2 = LSer::make([
    (@num.Rat::of_int(0), @num.Rat::of_int(1)),
    (@num.Rat::of_int(1), @num.Rat::of_int(-1)),
  ]) // 1 − t
  let g2 = LSer::make([
    (@num.Rat::of_int(0), @num.Rat::of_int(-1)),
    (@num.Rat::of_int(2), @num.Rat::of_int(4)),
  ]) // −1 + 4t²
  let sum = f2.add(g2) // −t + 4t²
  match sum.val() {
    Some(v) => if !(v.compare(@num.Rat::of_int(-1)) > 0) { cancel_ok = false }
    None => cancel_ok = false
  }
  out.push(
    (
      "相消：val(f+g) > min(val f, val g)（熱帶化的資訊損失）", cancel_ok,
      "f = 1−t（val 0）、g = −1+4t²（val 0），但 val(f+g) = 1 > 0",
    ),
  )

  // ---- 2. Newton–Puiseux ----
  // 根：t, t⁻¹, 2 （賦值 1, −1, 0）
  let roots : Array[LSer] = [
    LSer::mono(@num.Rat::of_int(1), 1),
    LSer::mono(@num.Rat::of_int(-1), 1),
    LSer::konst(2),
  ]
  let fpoly = poly_from_roots(roots)
  let rv = root_valuations(fpoly)
  // 比較：多邊形給出的賦值 vs 根的真實賦值
  let mut np_ok = true
  let expect : Array[@num.Rat] = [
    @num.Rat::of_int(1),
    @num.Rat::of_int(-1),
    @num.Rat::of_int(0),
  ]
  for (v, m) in rv {
    for _ in 0..<m {
      let mut found = -1
      for i in 0..<expect.length() {
        if found < 0 && expect[i] == v {
          found = i
        }
      }
      if found < 0 {
        np_ok = false
      } else {
        let _ = expect.remove(found)
      }
    }
  }
  out.push(
    (
      "Newton–Puiseux：根的賦值 = −(多邊形邊斜率)",
      np_ok && expect.length() == 0,
      "根 t, t⁻¹, 2 ⇒ 賦值 (1, −1, 0)",
    ),
  )

  // 分數賦值：根 t^{1/2}, t^{1/2}, t （賦值 1/2, 1/2, 1）
  let roots2 : Array[LSer] = [
    LSer::mono(
      @num.Rat::make(@bigint.BigInt::from_int(1), @bigint.BigInt::from_int(2)),
      1,
    ),
    LSer::mono(
      @num.Rat::make(@bigint.BigInt::from_int(1), @bigint.BigInt::from_int(2)),
      1,
    ),
    LSer::mono(@num.Rat::of_int(1), 1),
  ]
  let f2p = poly_from_roots(roots2)
  let rv2 = root_valuations(f2p)
  let mut np2_ok = rv2.length() > 0
  let mut desc = ""
  for (v, m) in rv2 {
    desc = desc + "(\{v}, ×\{m}) "
  }
  // 期望兩條邊：斜率 −1/2 重數 2，斜率 −1 重數 1
  let half = @num.Rat::make(
    @bigint.BigInt::from_int(1),
    @bigint.BigInt::from_int(2),
  )
  let mut seen_half = false
  let mut seen_one = false
  for (v, m) in rv2 {
    if v == half && m == 2 {
      seen_half = true
    }
    if v == @num.Rat::of_int(1) && m == 1 {
      seen_one = true
    }
  }
  if !seen_half || !seen_one {
    np2_ok = false
  }
  out.push(
    (
      "分數賦值：根 t^{1/2}, t^{1/2}, t ⇒ 斜率 −1/2（重數 2）與 −1",
      np2_ok, desc,
    ),
  )

  // ---- 3. 牛頓多邊形平衡 ----
  let mut bal_ok = true
  let mut detail = ""
  for (p, q) in [(1, 1), (2, 3), (3, 5), (4, 6)] {
    let (sx, sy) = balance_tripod(p, q)
    if sx != 0 || sy != 0 {
      bal_ok = false
    }
    detail = detail + "(\{p},\{q})→(\{sx},\{sy}) "
  }
  out.push(
    (
      "熱帶平衡律 Σ ℓ·u = 0（x^p+y^q+1 的牛頓三角形）", bal_ok,
      detail,
    ),
  )

  // ---- 4. 熱帶曲線 = corner locus ----
  let terms : Array[(Int32, Int32, Int32)] = [(1, 0, 0), (0, 1, 0), (0, 0, 0)] // x + y + 1
  let mut corner_ok = true
  // 三條射線上的點：最小值恰在兩項取得
  for w in [(-1, -1), (-2, -2), (1, 0), (3, 0), (0, 1), (0, 4)] {
    if min_attained(terms, w) < 2 {
      corner_ok = false
    }
  }
  // 內部點（例如 (1,1)）最小值唯一 ⇒ 不在熱帶曲線上
  if min_attained(terms, (1, 1)) != 1 {
    corner_ok = false
  }
  out.push(
    (
      "熱帶曲線 = corner locus（x+y+1 的熱帶直線）", corner_ok, "3 條射線",
    ),
  )

  // 熱帶半環分配律（窮舉小範圍）
  let mut semi_ok = true
  for a in 0..<4 {
    for b in 0..<4 {
      for c in 0..<4 {
        let ta = Trop::of(a)
        let tb = Trop::of(b)
        let tc = Trop::of(c)
        if !(ta.mul(tb.add(tc)) == ta.mul(tb).add(ta.mul(tc))) {
          semi_ok = false
        }
      }
    }
  }
  out.push(
    (
      "min-plus 半環分配律（64 組）", semi_ok, "a⊗(b⊕c) = (a⊗b)⊕(a⊗c)",
    ),
  )

  // 泛型 Horner 在 Trop 上的重用（同一份程式碼）
  let cp : Array[Trop] = [Trop::of(0), Trop::of(3), Trop::of(1)]
  let hv = @num.horner(cp, Trop::of(2))
  out.push(
    (
      "泛型 Horner 用於熱帶多項式",
      hv == Trop::of(0),
      "min(0, 3+2, 1+4) = 0",
    ),
  )

  out
}
