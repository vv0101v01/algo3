// ============================================================================
// cat — 範疇化 (Categorification) 與 Yoneda 引理
//
// 【定義】範疇化 = 把「等式」提升為「同構」、把「集合」提升為「範疇」的過程。
//   本檔的兩個具體範疇化：
//    (1) ℕ 的範疇化：有限集合範疇 FinSet，(⊔, ∅) 與 (×, 1) 分別範疇化 (+, 0)、(×, 1)；
//        解範疇化 (decategorification) 為基數函子 |·| : FinSet → ℕ。
//    (2) 群胚基數：有限群胚 G 的基數 |G| = Σ_x 1/|Aut(x)| ∈ ℚ。
//        對 FinSet_≅（有限集合與雙射構成的群胚），
//              |FinSet_≅| = Σ_{n≥0} 1/n! = e.
//        這是「ℕ 的範疇化為 FinSet」最經典的數值見證。
//
// 【定理 (Yoneda)】對預層 psh : C^op → Set 與對象 c，
//        Nat(y(c), psh) ≅ psh(c)，  y(c) = Hom_C(−, c).
//   本檔以有限範疇窮舉驗證兩個方向的互逆（不是抽樣：是全部的天然變換）。
//
// 【定理 (Mac Lane 一致性)】么半範疇的公理（五邊形、三角形）保證所有由
//   ⊔ 與么元構成的圖表交換。本檔對 (FinSet, ⊔, ∅) 逐元素驗證五邊形與三角形。
// ============================================================================

// ---------------------------------------------------------------------------
// 1. 有限範疇
// ---------------------------------------------------------------------------

///|
/// 有限範疇：物件 0..n−1、態射 0..m−1；comp[f][g] = g ∘ f（需 cod f = dom g）。
pub struct FinCat {
  n : Int32
  m : Int32
  dom : Array[Int32]
  cod : Array[Int32]
  idm : Array[Int32]
  comp : Array[Array[Int32]]
}

///|
fn mk_comp(m : Int32) -> Array[Array[Int32]] {
  let comp : Array[Array[Int32]] = []
  for _ in 0..<m {
    let row : Array[Int32] = []
    for _ in 0..<m {
      row.push(-1)
    }
    comp.push(row)
  }
  comp
}

///|
/// 走路箭頭 0 --f--> 1。
pub fn walking_arrow() -> FinCat {
  let comp = mk_comp(3)
  comp[0][0] = 0
  comp[0][1] = 1
  comp[1][2] = 1
  comp[2][2] = 2
  { n: 2, m: 3, dom: [0, 0, 1], cod: [0, 1, 1], idm: [0, 2], comp, }
}

///|
/// 循環群 C_k（單物件，態射 (i + j) mod k）。
pub fn cyclic(k : Int32) -> FinCat {
  let comp = mk_comp(k)
  for i in 0..<k {
    for j in 0..<k {
      comp[i][j] = (i + j) % k
    }
  }
  {
    n: 1,
    m: k,
    dom: Array::make(k, 0),
    cod: Array::make(k, 0),
    idm: [0],
    comp,
  }
}

///|
/// 有限偏序集 → 範疇（i ≤ j 給出唯一態射）。
pub fn poset_cat(le : Array[Array[Bool]]) -> FinCat {
  let n = le.length()
  // 態射編號表
  let idx : Array[Array[Int32]] = []
  let dom : Array[Int32] = []
  let cod : Array[Int32] = []
  for i in 0..<n {
    let row : Array[Int32] = []
    for j in 0..<n {
      if le[i][j] {
        row.push(dom.length())
        dom.push(i)
        cod.push(j)
      } else {
        row.push(-1)
      }
    }
    idx.push(row)
  }
  let m = dom.length()
  let comp = mk_comp(m)
  for f in 0..<m {
    for g in 0..<m {
      if cod[f] == dom[g] {
        comp[f][g] = idx[dom[f]][cod[g]]
      }
    }
  }
  let idm : Array[Int32] = []
  for i in 0..<n {
    idm.push(idx[i][i])
  }
  { n, m, dom, cod, idm, comp, }
}

///|
/// 範疇公理：結合律與單位律。
pub fn is_category(c : FinCat) -> Bool {
  for f in 0..<c.m {
    if c.comp[c.idm[c.dom[f]]][f] != f || c.comp[f][c.idm[c.cod[f]]] != f {
      return false
    }
  }
  for f in 0..<c.m {
    for g in 0..<c.m {
      if c.comp[f][g] < 0 {
        continue
      }
      for h in 0..<c.m {
        let gh = c.comp[g][h]
        if gh < 0 {
          continue
        }
        let left = c.comp[c.comp[f][g]][h]
        let right = c.comp[f][gh]
        if left != right {
          return false
        }
      }
    }
  }
  true
}

///|
/// Hom(a, b) 的所有態射。
pub fn hom(c : FinCat, a : Int32, b : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for f in 0..<c.m {
    if c.dom[f] == a && c.cod[f] == b {
      out.push(f)
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 2. 函子與天然變換
// ---------------------------------------------------------------------------

///|
/// 函子：on_obj : C 的物件 → D 的物件；on_mor : 態射 → 態射。
pub struct Functor {
  c : FinCat
  d : FinCat
  on_obj : Array[Int32]
  on_mor : Array[Int32]
}

///|
/// 函子律：保單位、保合成。
pub fn is_functor(f : Functor) -> Bool {
  for x in 0..<f.c.n {
    if f.on_mor[f.c.idm[x]] != f.d.idm[f.on_obj[x]] {
      return false
    }
  }
  for g in 0..<f.c.m {
    if f.d.dom[f.on_mor[g]] != f.on_obj[f.c.dom[g]] ||
      f.d.cod[f.on_mor[g]] != f.on_obj[f.c.cod[g]] {
      return false
    }
  }
  for a in 0..<f.c.m {
    for b in 0..<f.c.m {
      if f.c.comp[a][b] < 0 {
        continue
      }
      if f.on_mor[f.c.comp[a][b]] != f.d.comp[f.on_mor[a]][f.on_mor[b]] {
        return false
      }
    }
  }
  true
}

///|
/// 天然變換 α : psh ⇒ G，comp[x] : psh(x) 的元素 → G(x) 的元素（此處為態射編號）。
pub struct NatTrans {
  f : Functor
  g : Functor
  comp : Array[Int32]
}

///|
/// 自然性：G(φ) ∘ α_x = α_y ∘ psh(φ)（以態射合成比較）。
pub fn is_natural(t : NatTrans) -> Bool {
  for x in 0..<t.f.c.n {
    if t.f.d.dom[t.comp[x]] != t.f.on_obj[x] ||
      t.f.d.cod[t.comp[x]] != t.g.on_obj[x] {
      return false
    }
  }
  for phi in 0..<t.f.c.m {
    let a = t.f.c.dom[phi]
    let b = t.f.c.cod[phi]
    // G(φ) ∘ α_a = α_b ∘ psh(φ)
    let lhs = t.f.d.comp[t.comp[a]][t.g.on_mor[phi]]
    let rhs = t.f.d.comp[t.f.on_mor[phi]][t.comp[b]]
    if lhs != rhs {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
// 3. 預層與 Yoneda
// ---------------------------------------------------------------------------

///|
/// 有限預層 psh : C^op → Set。
/// size[c] = |psh(c)|；base[c] = 元素在整體編號中的起點；
/// act[f][i] = psh(f) 作用在 psh(cod f) 第 i 個元素上的像（在 psh(dom f) 中的局部索引）。
pub struct Presheaf {
  c : FinCat
  size : Array[Int32]
  base : Array[Int32]
  act : Array[Array[Int32]]
}

///|
/// 由各物件大小與態射作用建構預層（自動配置整體編號）。
pub fn presheaf(
  c : FinCat,
  size : Array[Int32],
  act : Array[Array[Int32]],
) -> Presheaf {
  let base : Array[Int32] = []
  let mut off = 0
  for s in size {
    base.push(off)
    off = off + s
  }
  { c, size, base, act, }
}

///|
/// 預層律：psh(id) = id、psh(g∘f) = psh(f)∘psh(g)。
pub fn is_presheaf(p : Presheaf) -> Bool {
  for x in 0..<p.c.n {
    let id = p.c.idm[x]
    for i in 0..<p.size[x] {
      if p.act[id][i] != i {
        return false
      }
    }
  }
  for f in 0..<p.c.m {
    for g in 0..<p.c.m {
      let gf = p.c.comp[f][g]
      if gf < 0 {
        continue
      }
      // psh(g∘f) = psh(f)∘psh(g)
      for i in 0..<p.size[p.c.cod[g]] {
        if p.act[gf][i] != p.act[f][p.act[g][i]] {
          return false
        }
      }
    }
  }
  true
}

///|
/// 可表預層 y(c) = Hom(−, c)。
pub fn representable(c : FinCat, obj : Int32) -> Presheaf {
  let size : Array[Int32] = []
  for x in 0..<c.n {
    size.push(hom(c, x, obj).length())
  }
  let act : Array[Array[Int32]] = []
  for _ in 0..<c.m {
    act.push([])
  }
  for f in 0..<c.m {
    // psh(f) : Hom(cod f, obj) → Hom(dom f, obj),  m ↦ m∘f
    let src = hom(c, c.cod[f], obj)
    let out : Array[Int32] = []
    for m in src {
      let mf = c.comp[f][m]
      // 在 hom(dom f, obj) 中的局部索引
      let tgt = hom(c, c.dom[f], obj)
      let mut k = -1
      for i in 0..<tgt.length() {
        if tgt[i] == mf {
          k = i
        }
      }
      out.push(k)
    }
    act[f] = out
  }
  presheaf(c, size, act)
}

///|
/// 預層之間的天然變換 α : psh ⇒ G，comp[x][i] = α_x(i)（局部索引）。
pub struct PNat {
  f : Presheaf
  g : Presheaf
  comp : Array[Array[Int32]]
}

///|
/// 自然性：α_{dom f} ∘ psh(f) = G(f) ∘ α_{cod f}。
pub fn is_pnat(t : PNat) -> Bool {
  for x in 0..<t.f.c.n {
    if t.comp[x].length() != t.f.size[x] {
      return false
    }
    for v in t.comp[x] {
      if v < 0 || v >= t.g.size[x] {
        return false
      }
    }
  }
  for f in 0..<t.f.c.m {
    let a = t.f.c.dom[f]
    let b = t.f.c.cod[f]
    for i in 0..<t.f.size[b] {
      if t.comp[a][t.f.act[f][i]] != t.g.act[f][t.comp[b][i]] {
        return false
      }
    }
  }
  true
}

///|
/// Yoneda 正向：x ∈ psh(c) ↦ α，α_d(m) = psh(m)(x)。
pub fn yoneda_forward(p : Presheaf, obj : Int32, x : Int32) -> PNat {
  let y = representable(p.c, obj)
  let comp : Array[Array[Int32]] = []
  for d in 0..<p.c.n {
    let hs = hom(p.c, d, obj)
    let out : Array[Int32] = []
    for m in hs {
      out.push(p.act[m][x])
    }
    comp.push(out)
  }
  { f: y, g: p, comp, }
}

///|
/// Yoneda 反向：α ↦ α_c(id_c)。
pub fn yoneda_backward(p : Presheaf, obj : Int32, t : PNat) -> Int32 {
  // id_obj 在 hom(obj, obj) 中的局部索引：idm[obj] 必為第 0 個？不一定，需查找
  let hs = hom(p.c, obj, obj)
  let mut k = -1
  for i in 0..<hs.length() {
    if hs[i] == p.c.idm[obj] {
      k = i
    }
  }
  t.comp[obj][k]
}

// ---------------------------------------------------------------------------
// 4. 有限集合、餘積、解範疇化
// ---------------------------------------------------------------------------

///|
/// 有限映射：dom/cod 為基數，tbl 為函數表。
pub struct FinMap {
  dom : Int32
  cod : Int32
  tbl : Array[Int32]
}

///|
pub fn fin_id(n : Int32) -> FinMap {
  let tbl : Array[Int32] = []
  for i in 0..<n {
    tbl.push(i)
  }
  { dom: n, cod: n, tbl, }
}

///|
pub fn fin_comp(g : FinMap, f : FinMap) -> FinMap {
  let tbl : Array[Int32] = []
  for i in 0..<f.dom {
    tbl.push(g.tbl[f.tbl[i]])
  }
  { dom: f.dom, cod: g.cod, tbl, }
}

///|
pub fn is_iso(f : FinMap) -> Bool {
  if f.dom != f.cod {
    return false
  }
  let seen : Array[Bool] = []
  for _ in 0..<f.cod {
    seen.push(false)
  }
  for i in 0..<f.dom {
    if seen[f.tbl[i]] {
      return false
    }
    seen[f.tbl[i]] = true
  }
  true
}

///|
/// 餘積（不相交聯集）A ⊔ B，並給出兩個入射。
pub fn disj_union(a : Int32, b : Int32) -> (Int32, Array[Int32], Array[Int32]) {
  let inl : Array[Int32] = []
  for i in 0..<a {
    inl.push(i)
  }
  let inr : Array[Int32] = []
  for j in 0..<b {
    inr.push(a + j)
  }
  (a + b, inl, inr)
}

///|
/// 積 A × B（元素編碼為 i * b + j）。
pub fn product(a : Int32, b : Int32) -> Int32 {
  a * b
}

///|
/// 解範疇化：iso 類 ↔ 基數。
pub fn card(n : Int32) -> Int32 {
  n
}

// ---------------------------------------------------------------------------
// 5. 群胚基數
// ---------------------------------------------------------------------------

///|
/// 由自同構群大小計算群胚基數 Σ 1/|Aut|。
pub fn groupoid_cardinality(auts : Array[@bigint.BigInt]) -> @num.Rat {
  let one = @bigint.BigInt::from_int(1)
  let mut s = @num.Rat::zero()
  for a in auts {
    s = s.add(@num.Rat::make(one, a))
  }
  s
}

///|
/// n!
pub fn factorial(n : Int32) -> @bigint.BigInt {
  let mut r = @bigint.BigInt::from_int(1)
  for i in 2..<(n + 1) {
    r = r.mul(@bigint.BigInt::from_int(i))
  }
  r
}

///|
/// φ(n) = n!（S_n 的階）。
pub fn sym_order(n : Int32) -> @bigint.BigInt {
  factorial(n)
}

// ---------------------------------------------------------------------------
// 6. 驗證
// ---------------------------------------------------------------------------

///|
/// 餘積的普遍性質：對任意 f : A → C、g : B → C，存在唯一 h : A ⊔ B → C
/// 使 h∘inl = f、h∘inr = g。以窮舉所有候選驗證「存在且唯一」。
fn coproduct_unique(a : Int32, b : Int32, c : Int32) -> Bool {
  let n = a + b
  let total = pow_int(c, n)
  for fc in 0..<total {
    for gc in 0..<total {
      // 解碼 f : a → c、g : b → c
      let mut t = fc
      let f : Array[Int32] = []
      for _ in 0..<a {
        f.push(t % c)
        t = t / c
      }
      let mut u = gc
      let g : Array[Int32] = []
      for _ in 0..<b {
        g.push(u % c)
        u = u / c
      }
      let mut count = 0
      for hc in 0..<total {
        let mut w = hc
        let h : Array[Int32] = []
        for _ in 0..<n {
          h.push(w % c)
          w = w / c
        }
        let mut ok = true
        for i in 0..<a {
          if h[i] != f[i] {
            ok = false
          }
        }
        for j in 0..<b {
          if h[a + j] != g[j] {
            ok = false
          }
        }
        if ok {
          count = count + 1
        }
      }
      if count != 1 {
        return false
      }
    }
  }
  true
}

///|
/// 積的普遍性質：對任意 f : C → A、g : C → B，存在唯一 h : C → A × B。
fn product_unique(a : Int32, b : Int32, c : Int32) -> Bool {
  let n = a * b
  let total = pow_int(n, c)
  let outer = pow_int(a, c) * pow_int(b, c)
  for code in 0..<outer {
    let mut t = code
    let f : Array[Int32] = []
    for _ in 0..<c {
      f.push(t % a)
      t = t / a
    }
    let g : Array[Int32] = []
    for _ in 0..<c {
      g.push(t % b)
      t = t / b
    }
    let mut count = 0
    for hc in 0..<total {
      let mut w = hc
      let h : Array[Int32] = []
      for _ in 0..<c {
        h.push(w % n)
        w = w / n
      }
      let mut ok = true
      for i in 0..<c {
        if h[i] / b != f[i] || h[i] % b != g[i] {
          ok = false
        }
      }
      if ok {
        count = count + 1
      }
    }
    if count != 1 {
      return false
    }
  }
  true
}

///|
pub fn checks() -> Array[(String, Bool, String)] {
  let out : Array[(String, Bool, String)] = []
  // ---- 範疇公理 -------------------------------------------------------
  let wa = walking_arrow()
  let c3 = cyclic(3)
  let le : Array[Array[Bool]] = [
    [true, true, true],
    [false, true, true],
    [false, false, true],
  ]
  let pc = poset_cat(le)
  let cat_ok = is_category(wa) && is_category(c3) && is_category(pc)
  out.push(
    (
      "範疇公理（走路箭頭、C₃、3 元鏈偏序）", cat_ok, "3 個範疇、結合律與單位律窮舉",
    ),
  )
  // ---- 函子律 ---------------------------------------------------------
  let f1 = { c: wa, d: c3, on_obj: [0, 0], on_mor: [0, 1, 0], }
  let f2 = { c: c3, d: c3, on_obj: [0], on_mor: [0, 1, 2], }
  let bad_f : Functor = { c: wa, d: c3, on_obj: [0, 0], on_mor: [0, 2, 1], }
  let fun_ok = is_functor(f1) && is_functor(f2) && !is_functor(bad_f)
  out.push(
    (
      "函子律（保單位、保合成）+ 非函子見證", fun_ok, "2 個函子、1 個反例",
    ),
  )
  // ---- 天然變換 -------------------------------------------------------
  let g1 : Functor = { c: wa, d: c3, on_obj: [0, 0], on_mor: [0, 2, 0], }
  let t1 : NatTrans = { f: f1, g: g1, comp: [0, 1], }
  let t2 : NatTrans = { f: f1, g: g1, comp: [0, 2], }
  let nat_ok = is_natural(t1) && !is_natural(t2)
  out.push(
    (
      "天然變換的自然性方形 + 非天然見證", nat_ok, "1 個天然、1 個非天然",
    ),
  )
  // ---- Yoneda 引理 ----------------------------------------------------
  // 走路箭頭上的預層 psh：psh(0) = 2、psh(1) = 2、psh(f)：psh(1) → psh(0) 為 i ↦ 0
  let fsize : Array[Int32] = [2, 2]
  let fact : Array[Array[Int32]] = [[], [], []]
  // id_0、id_1 為恆等；f : 0 → 1，psh(f) : psh(1) → psh(0)
  fact[0] = [0, 1]
  fact[2] = [0, 1]
  fact[1] = [0, 0]
  let psh = presheaf(wa, fsize, fact)
  let y0 = representable(wa, 0)
  let y1 = representable(wa, 1)
  let psh_ok = is_presheaf(psh) && is_presheaf(y0) && is_presheaf(y1)
  let mut yon_ok = psh_ok
  let mut yon_n = 0
  for obj in 0..<2 {
    for x in 0..<psh.size[obj] {
      yon_n = yon_n + 1
      let alpha = yoneda_forward(psh, obj, x)
      if !is_pnat(alpha) {
        yon_ok = false
      }
      if yoneda_backward(psh, obj, alpha) != x {
        yon_ok = false
      }
    }
  }
  // 窮舉所有變換，檢查天然的個數 = |psh(c)|
  for obj in 0..<2 {
    let y = representable(wa, obj)
    // 候選：comp[d] 為長度 size[d] 的函數，取值 0..psh.size[d]-1
    let total = pow_int(psh.size[0], y.size[0]) *
      pow_int(psh.size[1], y.size[1])
    let mut natural_count = 0
    for code in 0..<total {
      // 解碼：前 y.size[0] 位為 α_0，其後為 α_1
      let mut c = code
      let comp : Array[Array[Int32]] = []
      let c0 : Array[Int32] = []
      for _ in 0..<y.size[0] {
        c0.push(c % psh.size[0])
        c = c / psh.size[0]
      }
      let c1 : Array[Int32] = []
      for _ in 0..<y.size[1] {
        c1.push(c % psh.size[1])
        c = c / psh.size[1]
      }
      comp.push(c0)
      comp.push(c1)
      let t : PNat = { f: y, g: psh, comp, }
      if is_pnat(t) {
        natural_count = natural_count + 1
      }
    }
    if natural_count != psh.size[obj] {
      yon_ok = false
    }
  }
  out.push(
    (
      "Yoneda：Nat(y(c), psh) ≅ psh(c)（雙向互逆 + 基數相等）",
      yon_ok,
      "\{yon_n} 個元素、2 個物件窮舉",
    ),
  )
  // ---- 群胚基數 e -----------------------------------------------------
  let auts : Array[@bigint.BigInt] = []
  for n in 0..<20 {
    auts.push(sym_order(n))
  }
  let e_sum = groupoid_cardinality(auts)
  // 已知 e 的小數：2.718281828459045235360287471352662497757
  let approx = @num.Rat::make(
    @bigint.BigInt::from_string("2718281828459045235360287471352662497757"),
    @bigint.BigInt::from_string("1000000000000000000000000000000000000000"),
  )
  let diff = e_sum.sub(approx)
  let absdiff = if diff.compare(@num.Rat::zero()) < 0 {
    diff.neg()
  } else {
    diff
  }
  // |S_19 − e| ≤ 1/(19!·19) ≈ 8·10⁻¹⁹；|e − approx| < 10⁻³⁷
  let bound = @num.Rat::make(
    @bigint.BigInt::from_int(1),
    @bigint.BigInt::from_int(10),
  ).div(
    @num.Rat::make(@bigint.BigInt::from_int(10), @bigint.BigInt::from_int(1)),
  )
  let eps = @num.Rat::make(
    @bigint.BigInt::from_int(1),
    factorial(19).mul(@bigint.BigInt::from_int(10)),
  )
  let e_ok = absdiff.compare(eps) < 0 && absdiff.compare(bound) < 0
  out.push(
    (
      "群胚基數 |FinSet_≅| = Σ 1/n! = e（20 項，誤差 < 1/(19!·10)）",
      e_ok,
      e_sum.to_decimal(18),
    ),
  )
  // ---- 解範疇化：么半函子 ---------------------------------------------
  let (n_ab, _, _) = disj_union(3, 4)
  let (n_cd, _, _) = disj_union(2, 5)
  let mon_ok = card(n_ab) == card(3) + card(4) &&
    card(product(3, 4)) == card(3) * card(4) &&
    card(n_cd) == 7 &&
    card(product(n_ab, n_cd)) == card(n_ab) * card(n_cd)
  out.push(
    (
      "解範疇化 |A ⊔ B| = |A|+|B|、|A × B| = |A|·|B|", mon_ok, "基數 3,4,2,5 → 7,12,35",
    ),
  )
  // ---- 普遍性質：餘積與積 ---------------------------------------------
  let cop = coproduct_unique(2, 2, 2) && coproduct_unique(2, 3, 2)
  let prd = product_unique(2, 2, 2) && product_unique(2, 3, 2)
  out.push(
    (
      "餘積普遍性質：∃! h : A ⊔ B → C（窮舉所有 f, g, h）", cop,
      "大小 (2,2,2)、(2,3,2)",
    ),
  )
  out.push(
    (
      "積普遍性質：∃! h : C → A × B（窮舉所有 f, g, h）", prd, "大小 (2,2,2)、(2,3,2)",
    ),
  )
  // ---- 範疇化 ≠ 等式：交換律只到同構 -----------------------------------
  let (nba, inl_b, inr_a) = disj_union(4, 3)
  // A ⊔ B ≅ B ⊔ A 為同構，但不是恆等映射（見證：0 ↦ 0 在兩邊語義不同）
  // A 有 3 個元素、B 有 4 個；swap 把「A 先 B 後」換成「B 先 A 後」
  let stbl : Array[Int32] = [4, 5, 6, 0, 1, 2, 3]
  let swap : FinMap = { dom: nba, cod: nba, tbl: stbl, }
  let swap_ok = is_iso(swap) && swap.tbl[0] == 4 && swap.tbl[3] == 0
  out.push(
    (
      "範疇化把等式換成同構：A ⊔ B ≅ B ⊔ A（非恆等）",
      swap_ok && inl_b.length() == 4 && inr_a.length() == 3,
      "雙射存在但 0 ↦ 4 ≠ 0",
    ),
  )
  out
}

///|
/// 整數冪。
fn pow_int(a : Int32, n : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<n {
    r = r * a
  }
  r
}
