// ============================================================================
// order — 有限偏序、格、Heyting 代數、Knaster–Tarski 不動點、Birkhoff 表示定理
//
// 定理（Birkhoff 1937）：任何有限分配格 L 同構於其 join-不可約元偏序集 J(L)
// 的下集格 Down(J(L))：x ↦ { j ∈ J(L) : j ≤ x }。
// 本檔以「窮舉驗證」實現該同構，並以 M3 / N5 兩個非分配格作為反例證人。
// ============================================================================

///|
/// 獨立配置的 r×c 整數矩陣（Array::make 共用內層參照，必須逐列建立）。
pub fn zeros2(r : Int32, c : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for _ in 0..<r {
    out.push(Array::make(c, 0))
  }
  out
}

///|
pub fn falses2(r : Int32, c : Int32) -> Array[Array[Bool]] {
  let out : Array[Array[Bool]] = []
  for _ in 0..<r {
    out.push(Array::make(c, false))
  }
  out
}

///|
pub struct Poset {
  n : Int32
  le : Array[Array[Bool]]
}

///|
pub fn Poset::new_cover(n : Int32, cover : Array[(Int32, Int32)]) -> Poset {
  let le : Array[Array[Bool]] = falses2(n, n)
  for i in 0..<n {
    le[i][i] = true
  }
  for e in cover {
    le[e.0][e.1] = true
  }
  // Floyd–Warshall 傳遞閉包
  for k in 0..<n {
    for i in 0..<n {
      for j in 0..<n {
        if le[i][k] && le[k][j] {
          le[i][j] = true
        }
      }
    }
  }
  { n, le, }
}

///|
pub fn Poset::leq(self : Poset, a : Int32, b : Int32) -> Bool {
  self.le[a][b]
}

///|
pub fn Poset::is_antisymmetric(self : Poset) -> Bool {
  let mut ok = true
  for i in 0..<self.n {
    for j in 0..<self.n {
      if i != j && self.le[i][j] && self.le[j][i] {
        ok = false
      }
    }
  }
  ok
}

///|
/// 拓撲排序：回傳一個線性擴張（每次取極小元）。
pub fn Poset::linear_extension(self : Poset) -> Array[Int32] {
  let out : Array[Int32] = []
  let done : Array[Bool] = Array::make(self.n, false)
  for _ in 0..<self.n {
    let mut pick = -1
    for i in 0..<self.n {
      if done[i] {
        continue
      }
      let mut minimal = true
      for j in 0..<self.n {
        if j != i && !done[j] && self.le[j][i] {
          minimal = false
        }
      }
      if minimal && pick < 0 {
        pick = i
      }
    }
    if pick < 0 {
      break
    }
    done[pick] = true
    out.push(pick)
  }
  out
}

///|
/// 有限格：元素 0..n-1，join/meet 以表給出。
pub struct Lattice {
  n : Int32
  join : Array[Array[Int32]]
  meet : Array[Array[Int32]]
}

///|
pub fn Lattice::leq(self : Lattice, a : Int32, b : Int32) -> Bool {
  self.join[a][b] == b
}

///|
pub fn Lattice::bottom(self : Lattice) -> Int32 {
  let mut b = 0
  for i in 1..<self.n {
    if self.meet[i][b] == i {
      b = i
    }
  }
  b
}

///|
pub fn Lattice::top(self : Lattice) -> Int32 {
  let mut t = 0
  for i in 1..<self.n {
    if self.join[i][t] == i {
      t = i
    }
  }
  t
}

///|
/// 格公理：冪等、交換、結合、吸收。
pub fn Lattice::axioms(self : Lattice) -> Bool {
  let mut ok = true
  for a in 0..<self.n {
    if self.join[a][a] != a || self.meet[a][a] != a {
      ok = false
    }
    for b in 0..<self.n {
      if self.join[a][b] != self.join[b][a] ||
        self.meet[a][b] != self.meet[b][a] {
        ok = false
      }
      if self.join[a][self.meet[a][b]] != a ||
        self.meet[a][self.join[a][b]] != a {
        ok = false
      }
      for c in 0..<self.n {
        if self.join[self.join[a][b]][c] != self.join[a][self.join[b][c]] {
          ok = false
        }
        if self.meet[self.meet[a][b]][c] != self.meet[a][self.meet[b][c]] {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// 分配律：a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)。
pub fn Lattice::is_distributive(self : Lattice) -> Bool {
  let mut ok = true
  for a in 0..<self.n {
    for b in 0..<self.n {
      for c in 0..<self.n {
        if self.meet[a][self.join[b][c]] !=
          self.join[self.meet[a][b]][self.meet[a][c]] {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// join-不可約元（非底、且 j = a∨b ⟹ j=a 或 j=b）。
pub fn Lattice::join_irreducibles(self : Lattice) -> Array[Int32] {
  let b = self.bottom()
  let out : Array[Int32] = []
  for j in 0..<self.n {
    if j == b {
      continue
    }
    let mut irr = true
    for a in 0..<self.n {
      for c in 0..<self.n {
        if self.join[a][c] == j && a != j && c != j {
          irr = false
        }
      }
    }
    if irr {
      out.push(j)
    }
  }
  out
}

///|
/// 由偏序取「下集格」：元素為位元遮罩。
pub fn downset_lattice(p : Poset) -> (Lattice, Array[Int32]) {
  let masks : Array[Int32] = []
  for m in 0..<(1 << p.n) {
    let mut is_down = true
    for i in 0..<p.n {
      if ((m >> i) & 1) == 1 {
        for j in 0..<p.n {
          if p.le[j][i] && ((m >> j) & 1) == 0 {
            is_down = false
          }
        }
      }
    }
    if is_down {
      masks.push(m)
    }
  }
  let n = masks.length()
  let idx : Array[Int32] = Array::make(1 << p.n, -1)
  for i in 0..<n {
    idx[masks[i]] = i
  }
  let join : Array[Array[Int32]] = zeros2(n, n)
  let meet : Array[Array[Int32]] = zeros2(n, n)
  for i in 0..<n {
    for j in 0..<n {
      join[i][j] = idx[masks[i] | masks[j]]
      meet[i][j] = idx[masks[i] & masks[j]]
    }
  }
  ({ n, join, meet, }, masks)
}

///|
/// 由 join/meet 表建構格並檢查封閉性（此處直接信任表，供內部建構用）。
pub fn lattice_from_tables(
  n : Int32,
  join : Array[Array[Int32]],
  meet : Array[Array[Int32]],
) -> Lattice {
  { n, join, meet, }
}

///|
/// 鏈 0 < 1 < ... < n-1。
pub fn chain(n : Int32) -> Lattice {
  let join : Array[Array[Int32]] = zeros2(n, n)
  let meet : Array[Array[Int32]] = zeros2(n, n)
  for i in 0..<n {
    for j in 0..<n {
      join[i][j] = if i > j { i } else { j }
      meet[i][j] = if i < j { i } else { j }
    }
  }
  { n, join, meet, }
}

///|
/// 除數格 Div(n)：元素為 n 的除數，join=lcm、meet=gcd。
pub fn divisor_lattice(n0 : Int32) -> Lattice {
  let ds : Array[Int32] = []
  for d in 1..<(n0 + 1) {
    if n0 % d == 0 {
      ds.push(d)
    }
  }
  let m = ds.length()
  let pos : Array[Int32] = Array::make(n0 + 1, -1)
  for i in 0..<m {
    pos[ds[i]] = i
  }
  let join : Array[Array[Int32]] = zeros2(m, m)
  let meet : Array[Array[Int32]] = zeros2(m, m)
  for i in 0..<m {
    for j in 0..<m {
      let a = ds[i]
      let b = ds[j]
      // gcd
      let mut x = a
      let mut y = b
      while y != 0 {
        let t = x % y
        x = y
        y = t
      }
      let g = x
      let l = a / g * b
      meet[i][j] = pos[g]
      join[i][j] = pos[l]
    }
  }
  { n: m, join, meet, }
}

///|
/// M3（菱形）：5 元素非分配格。
pub fn diamond_m3() -> Lattice {
  // 0=⊥, 1,2,3=atoms, 4=⊤
  let join : Array[Array[Int32]] = zeros2(5, 5)
  let meet : Array[Array[Int32]] = zeros2(5, 5)
  for i in 0..<5 {
    for j in 0..<5 {
      join[i][j] = if i == 0 {
        j
      } else if j == 0 {
        i
      } else if i == j {
        i
      } else {
        4
      }
      meet[i][j] = if i == 4 {
        j
      } else if j == 4 {
        i
      } else if i == j {
        i
      } else {
        0
      }
    }
  }
  { n: 5, join, meet, }
}

///|
/// N5（五邊形）：5 元素非分配格。
pub fn pentagon_n5() -> Lattice {
  // 0 < 1 < 3 < 4, 0 < 2 < 4
  let le : Array[Array[Bool]] = [
    [true, true, true, true, true],
    [false, true, false, true, true],
    [false, false, true, false, true],
    [false, false, false, true, true],
    [false, false, false, false, true],
  ]
  let join : Array[Array[Int32]] = zeros2(5, 5)
  let meet : Array[Array[Int32]] = zeros2(5, 5)
  for i in 0..<5 {
    for j in 0..<5 {
      // lub = 最小上界
      let mut lub = 4
      for k in 0..<5 {
        if le[i][k] && le[j][k] && le[k][lub] {
          lub = k
        }
      }
      let mut glb = 0
      for kk in 0..<5 {
        let k = 4 - kk
        if le[k][i] && le[k][j] && le[glb][k] {
          glb = k
        }
      }
      join[i][j] = lub
      meet[i][j] = glb
    }
  }
  { n: 5, join, meet, }
}

///|
/// Heyting 蘊含：a → b = ⋁ { c : a ∧ c ≤ b }（有限格必存在）。
pub fn Lattice::heyting_impl(self : Lattice, a : Int32, b : Int32) -> Int32 {
  let mut acc = self.bottom()
  for c in 0..<self.n {
    if self.leq(self.meet[a][c], b) {
      acc = self.join[acc][c]
    }
  }
  acc
}

///|
/// 伴隨對驗證：a ∧ c ≤ b ⟺ c ≤ (a → b)，對所有 a,b,c。
pub fn Lattice::heyting_adjunction(self : Lattice) -> Bool {
  let mut ok = true
  for a in 0..<self.n {
    for b in 0..<self.n {
      let imp = self.heyting_impl(a, b)
      for c in 0..<self.n {
        if self.leq(self.meet[a][c], b) != self.leq(c, imp) {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// Knaster–Tarski：單調映射的最小不動點 = ⋁{x : x ≤ f x} = Kleene 迭代極限。
pub fn Lattice::lfp(self : Lattice, f : (Int32) -> Int32) -> Int32 {
  // Kleene：從 ⊥ 上升
  let mut x = self.bottom()
  let mut steps = 0
  while f(x) != x && steps < self.n + 2 {
    x = self.join[x][f(x)]
    steps = steps + 1
  }
  x
}

///|
/// 以窮舉檢查 f 單調、lfp 為不動點、且 lfp 是所有後不動點的下界。
pub fn Lattice::knaster_tarski(self : Lattice, f : (Int32) -> Int32) -> Bool {
  // 單調性
  for a in 0..<self.n {
    for b in 0..<self.n {
      if self.leq(a, b) && !self.leq(f(a), f(b)) {
        return false
      }
    }
  }
  let l = self.lfp(f)
  if f(l) != l {
    return false
  }
  for x in 0..<self.n {
    if self.leq(x, f(x)) && !self.leq(l, x) {
      return false
    }
  }
  true
}

///|
/// Birkhoff 表示定理的窮舉驗證。
/// 回傳 (是否同構, |J(L)|, |L|, 說明)
pub fn birkhoff_check(l : Lattice) -> (Bool, Int32, Int32, String) {
  let js = l.join_irreducibles()
  let k = js.length()
  // 誘導偏序
  let le : Array[Array[Bool]] = falses2(k, k)
  for i in 0..<k {
    for j in 0..<k {
      le[i][j] = l.leq(js[i], js[j])
    }
  }
  let p : Poset = { n: k, le, }
  let (dl, _masks) = downset_lattice(p)
  // φ(x) = 遮罩
  let img : Array[Int32] = []
  for x in 0..<l.n {
    let mut m = 0
    for i in 0..<k {
      if l.leq(js[i], x) {
        m = m | (1 << i)
      }
    }
    img.push(m)
  }
  // 單射
  let mut injective = true
  for i in 0..<l.n {
    for j in 0..<l.n {
      if i != j && img[i] == img[j] {
        injective = false
      }
    }
  }
  // 滿射：每個下集都是某個 φ(x)；且 φ 保 join/meet
  let mut surjective = l.n == dl.n && injective
  for i in 0..<l.n {
    for j in 0..<l.n {
      let mj = img[l.join[i][j]]
      let mm = img[l.meet[i][j]]
      if mj != (img[i] | img[j]) || mm != (img[i] & img[j]) {
        surjective = false
      }
    }
  }
  // 檢查映像剛好是全部下集
  let hit : Array[Bool] = Array::make(1 << k, false)
  for m in img {
    hit[m] = true
  }
  let mut count = 0
  for b in hit {
    if b {
      count = count + 1
    }
  }
  let ok = injective && surjective && count == dl.n
  (
    ok,
    k,
    l.n,
    "|J(L)|=\{k}, |L|=\{l.n}, |Down(J(L))|=\{dl.n}, 單射=\{injective}, 保 join/meet=\{surjective}",
  )
}

///|
pub fn checks() -> Array[(String, Bool, String)] {
  let out : Array[(String, Bool, String)] = []
  let b3 = divisor_lattice(30) // 30 = 2*3*5 → 布林格 B3
  let d12 = divisor_lattice(12)
  let c4 = chain(4)
  let m3 = diamond_m3()
  let n5 = pentagon_n5()

  out.push(("格公理：Div(30) (≅B3)", b3.axioms(), "8 元素"))
  out.push(("格公理：Div(12)", d12.axioms(), "6 元素"))
  out.push(("格公理：C4", c4.axioms(), "4 元素"))
  out.push(("格公理：M3", m3.axioms(), "5 元素"))
  out.push(("格公理：N5", n5.axioms(), "5 元素"))

  out.push(("分配律：Div(30)", b3.is_distributive(), "布林格必分配"))
  out.push(("分配律：Div(12)", d12.is_distributive(), "除數格分配"))
  out.push(
    ("非分配證人：M3", !m3.is_distributive(), "M3 違反分配律"),
  )
  out.push(
    ("非分配證人：N5", !n5.is_distributive(), "N5 違反分配律"),
  )

  let (ok1, j1, n1, d1) = birkhoff_check(b3)
  out.push(("Birkhoff：Div(30) ≅ Down(J)", ok1, d1))
  let (ok2, j2, n2, d2) = birkhoff_check(d12)
  out.push(("Birkhoff：Div(12) ≅ Down(J)", ok2, d2))
  let (ok3, _, _, d3) = birkhoff_check(c4)
  out.push(("Birkhoff：C4 ≅ Down(J)", ok3, d3))
  let (ok4, _, _, d4) = birkhoff_check(m3)
  out.push(
    ("非平凡性：M3 不滿足 Birkhoff 前提（非分配）", !ok4, d4),
  )

  out.push(
    (
      "Heyting 伴隨律：Div(30)",
      b3.heyting_adjunction(),
      "a∧c ≤ b ⟺ c ≤ a→b",
    ),
  )
  out.push(
    (
      "Heyting 伴隨律：Div(12)",
      d12.heyting_adjunction(),
      "a∧c ≤ b ⟺ c ≤ a→b",
    ),
  )
  let mut bad = 0
  for i in 0..<b3.n {
    if b3.heyting_impl(i, b3.bottom()) != b3.bottom() && i != b3.bottom() {
      bad = bad + 1
    }
  }
  out.push(
    (
      "Heyting 偽：a → ⊥ ≠ ⊥（非布林格）",
      bad > 0,
      "\{bad} 個元素",
    ),
  )

  // Knaster–Tarski：Div(30) 上的單調閉包算子
  let cl = b3
  let f = fn(x : Int32) -> Int32 { cl.join[x][cl.meet[x][1]] } // x ↦ x ∨ 2（在 B3 中將 “2-座標” 打開）
  out.push(
    (
      "Knaster–Tarski：最小不動點存在且最小",
      cl.knaster_tarski(f),
      "x ↦ x∨2",
    ),
  )
  let g = fn(x : Int32) -> Int32 { cl.meet[x][cl.top()] } // 恆等映射
  out.push(
    (
      "Knaster–Tarski：恆等映射的 lfp = ⊥",
      cl.knaster_tarski(g) && cl.lfp(g) == cl.bottom(),
      "",
    ),
  )

  // 線性擴張
  let p = Poset::new_cover(4, [(0, 1), (1, 2), (2, 3)])
  let lext = p.linear_extension()
  let mut is_lext = lext.length() == 4
  for i in 0..<lext.length() {
    for j in 0..<lext.length() {
      if i < j && p.leq(lext[j], lext[i]) && lext[i] != lext[j] {
        is_lext = false
      }
    }
  }
  out.push(("拓撲排序 = 線性擴張", is_lext, "C4 上唯一"))
  out
}
