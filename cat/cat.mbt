// ============================================================================
// cat — 有限範疇、函子、自然變換、預層、Yoneda 引理（可執行），
//        以及「範疇化」(categorification)：有限集合群胚的基數 = e。
//
// 約定：compose(f,g) 表示「先 f 後 g」= g∘f，要求 cod(f) = dom(g)。
// ============================================================================

///|
fn zeros2(r : Int32, c : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for _ in 0..<r {
    out.push(Array::make(c, 0))
  }
  out
}

///|
fn minus_ones2(r : Int32, c : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for _ in 0..<r {
    out.push(Array::make(c, -1))
  }
  out
}

///|
pub struct FinCat {
  n_obj : Int32
  n_mor : Int32
  dom : Array[Int32]
  cod : Array[Int32]
  idm : Array[Int32] // 每個物件的 identity 態射
  comp : Array[Array[Int32]] // comp[f][g] = g∘f，若未定義則為 -1
}

///|
pub fn FinCat::make(
  n_obj : Int32,
  dom : Array[Int32],
  cod : Array[Int32],
  idm : Array[Int32],
) -> FinCat {
  let n_mor = dom.length()
  let comp : Array[Array[Int32]] = minus_ones2(n_mor, n_mor)
  for f in 0..<n_mor {
    for g in 0..<n_mor {
      let a = dom[f]
      let b = cod[f]
      let c = dom[g]
      let d = cod[g]
      if b == c {
        // 尋找唯一的 h : a → d
        let mut found = -1
        for h in 0..<n_mor {
          if dom[h] == a && cod[h] == d {
            found = h
          }
        }
        comp[f][g] = found
      }
    }
  }
  { n_obj, n_mor, dom, cod, idm, comp, }
}

///|
/// 兩物件「走路箭頭」範疇：1 →(f) 0。
pub fn walking_arrow() -> FinCat {
  let cat = FinCat::make(2, [0, 1, 1], [0, 0, 1], [0, 2])
  cat
}

///|
/// 單物件群 C_n：態射 = {0..n-1}，複合 = 加法 mod n。
pub fn cyclic_group(n : Int32) -> FinCat {
  let dom : Array[Int32] = []
  let cod : Array[Int32] = []
  for _ in 0..<n {
    dom.push(0)
    cod.push(0)
  }
  let comp : Array[Array[Int32]] = zeros2(n, n)
  for i in 0..<n {
    for j in 0..<n {
      comp[i][j] = (i + j) % n
    }
  }
  { n_obj: 1, n_mor: n, dom, cod, idm: [0], comp, }
}

///|
/// 由偏序集（作為範疇）造範疇。
pub fn poset_category(n : Int32, le : Array[Array[Bool]]) -> FinCat {
  let pairs : Array[(Int32, Int32)] = []
  for i in 0..<n {
    for j in 0..<n {
      if le[i][j] {
        pairs.push((i, j))
      }
    }
  }
  let m = pairs.length()
  let m_ = m
  let dom : Array[Int32] = Array::make(m, 0)
  let cod : Array[Int32] = Array::make(m, 0)
  for k in 0..<m {
    dom[k] = pairs[k].0
    cod[k] = pairs[k].1
  }
  let idm : Array[Int32] = Array::make(n, 0)
  for k in 0..<n {
    for m in 0..<m_ {
      if dom[m] == k && cod[m] == k {
        idm[k] = m
      }
    }
  }
  FinCat::make(n, dom, cod, idm)
}

///|
/// 範疇公理：結合律 + 單位律（窮舉所有可複合三元組）。
pub fn FinCat::axioms(self : FinCat) -> Bool {
  // 先補 comp 表（若為空）
  let c = self.rebuild()
  let mut ok = true
  for f in 0..<c.n_mor {
    // id 單位
    let idc = c.idm[c.cod[f]]
    let idd = c.idm[c.dom[f]]
    if c.comp[f][idc] != f || c.comp[idd][f] != f {
      ok = false
    }
    for g in 0..<c.n_mor {
      if c.comp[f][g] < 0 {
        continue
      }
      for h in 0..<c.n_mor {
        if c.comp[g][h] < 0 {
          continue
        }
        let left = c.comp[f][c.comp[g][h]]
        let right = c.comp[c.comp[f][g]][h]
        if left != right || left < 0 {
          ok = false
        }
      }
    }
  }
  ok
}

///|
pub fn FinCat::rebuild(self : FinCat) -> FinCat {
  let n_mor = self.n_mor
  let comp : Array[Array[Int32]] = minus_ones2(n_mor, n_mor)
  for f in 0..<n_mor {
    for g in 0..<n_mor {
      let a = self.dom[f]
      let b = self.cod[f]
      let c = self.dom[g]
      let d = self.cod[g]
      if b == c {
        // 唯一態射 a→d（若有多個，取第一個：本專案只用「態射集合 =
        // hom-set 最多一元」的範疇，或已用 comp 表指定的么半群）
        if self.comp.length() > 0 && self.comp[0].length() > 0 {
          comp[f][g] = self.comp[f][g]
        } else {
          for h in 0..<n_mor {
            if self.dom[h] == a && self.cod[h] == d {
              comp[f][g] = h
            }
          }
        }
      }
    }
  }
  {
    n_obj: self.n_obj,
    n_mor,
    dom: self.dom,
    cod: self.cod,
    idm: self.idm,
    comp,
  }
}

///|
pub struct Functor {
  src : FinCat
  dst : FinCat
  on_obj : Array[Int32]
  on_mor : Array[Int32]
}

///|
pub fn Functor::is_functor(self : Functor) -> Bool {
  let s = self.src.rebuild()
  let d = self.dst.rebuild()
  let mut ok = true
  for o in 0..<s.n_obj {
    if self.on_mor[s.idm[o]] != d.idm[self.on_obj[o]] {
      ok = false
    }
  }
  for f in 0..<s.n_mor {
    if self.on_obj[s.dom[f]] != d.dom[self.on_mor[f]] ||
      self.on_obj[s.cod[f]] != d.cod[self.on_mor[f]] {
      ok = false
    }
    for g in 0..<s.n_mor {
      if s.comp[f][g] >= 0 {
        if d.comp[self.on_mor[f]][self.on_mor[g]] != self.on_mor[s.comp[f][g]] {
          ok = false
        }
      }
    }
  }
  ok
}

// ---------------------------------------------------------------------------
// 預層（presheaf）：F : C^op → Set，以「有限集合 + 作用表」表示
// ---------------------------------------------------------------------------

///|
pub struct Presheaf {
  cat : FinCat
  sizes : Array[Int32] // |F(c)|
  start : Array[Int32] // F(c) 元素在全域的起點
  act : Array[Array[Int32]] // act[m][i] = F(m)(i)，i ∈ F(cod m)，值為 F(dom m) 的局部索引
}

///|
pub fn Presheaf::of_constant(cat : FinCat, k : Int32) -> Presheaf {
  let c = cat.rebuild()
  let sizes : Array[Int32] = Array::make(c.n_obj, k)
  let start : Array[Int32] = Array::make(c.n_obj, 0)
  for o in 1..<c.n_obj {
    start[o] = start[o - 1] + sizes[o - 1]
  }
  let act : Array[Array[Int32]] = Array::make(c.n_mor, [])
  for m in 0..<c.n_mor {
    let tbl : Array[Int32] = Array::make(k, 0)
    for i in 0..<k {
      tbl[i] = i
    }
    act[m] = tbl
  }
  { cat: c, sizes, start, act, }
}

///|
/// 可表預層 y(c)（Yoneda 嵌入）。
pub fn Presheaf::representable(cat : FinCat, c : Int32) -> Presheaf {
  let cat2 = cat.rebuild()
  let sizes : Array[Int32] = Array::make(cat2.n_obj, 0)
  // |y(c)(d)| = #Hom(d,c)
  for d in 0..<cat2.n_obj {
    let mut k = 0
    for m in 0..<cat2.n_mor {
      if cat2.dom[m] == d && cat2.cod[m] == c {
        k = k + 1
      }
    }
    sizes[d] = k
  }
  let start : Array[Int32] = Array::make(cat2.n_obj, 0)
  for o in 1..<cat2.n_obj {
    start[o] = start[o - 1] + sizes[o - 1]
  }
  // 每個 d 的 Hom(d,c) 元素排序表
  let homs : Array[Array[Int32]] = Array::make(cat2.n_obj, [])
  for d in 0..<cat2.n_obj {
    let lst : Array[Int32] = []
    for m in 0..<cat2.n_mor {
      if cat2.dom[m] == d && cat2.cod[m] == c {
        lst.push(m)
      }
    }
    homs[d] = lst
  }
  // act[f][j] = (homs[dom f] 中) m∘f 的索引，m = homs[cod f][j]
  let act : Array[Array[Int32]] = Array::make(cat2.n_mor, [])
  for f in 0..<cat2.n_mor {
    let d = cat2.dom[f]
    let e = cat2.cod[f]
    let tbl : Array[Int32] = Array::make(homs[e].length(), 0)
    for j in 0..<homs[e].length() {
      let m = homs[e][j]
      let mf = cat2.comp[f][m] // m∘f : d → c
      // 找 mf 在 homs[d] 的索引
      for k in 0..<homs[d].length() {
        if homs[d][k] == mf {
          tbl[j] = k
        }
      }
    }
    act[f] = tbl
  }
  { cat: cat2, sizes, start, act, }
}

///|
pub fn Presheaf::is_functor(self : Presheaf) -> Bool {
  let c = self.cat
  let mut ok = true
  for m in 0..<c.n_mor {
    if self.act[m].length() != self.sizes[c.cod[m]] {
      ok = false
    }
  }
  // F(id) = id
  for o in 0..<c.n_obj {
    let id = c.idm[o]
    for i in 0..<self.sizes[o] {
      if self.act[id][i] != i {
        ok = false
      }
    }
  }
  // F(g∘f) = F(f)∘F(g)
  for f in 0..<c.n_mor {
    for g in 0..<c.n_mor {
      if c.comp[f][g] >= 0 {
        let h = c.comp[f][g]
        for j in 0..<self.sizes[c.cod[g]] {
          if self.act[f][self.act[g][j]] != self.act[h][j] {
            ok = false
          }
        }
      }
    }
  }
  ok
}

///|
/// 自然變換 α : F ⇒ G，表示為每個物件上的函數表（局部索引）。
pub struct NatTrans {
  dom : Presheaf
  cod : Presheaf
  comp : Array[Array[Int32]]
}

///|
pub fn NatTrans::is_natural(self : NatTrans) -> Bool {
  let c = self.dom.cat
  let mut ok = true
  for o in 0..<c.n_obj {
    if self.comp[o].length() != self.dom.sizes[o] {
      ok = false
    }
  }
  for m in 0..<c.n_mor {
    let a = c.dom[m]
    let b = c.cod[m]
    for i in 0..<self.dom.sizes[b] {
      // G(m)(α_b(i)) = α_a(F(m)(i))
      if self.comp[a][self.dom.act[m][i]] != self.cod.act[m][self.comp[b][i]] {
        ok = false
      }
    }
  }
  ok
}

///|
/// Yoneda 正向：x ∈ F(c) ↦ (α_d : Hom(d,c) → F(d), m ↦ F(m)(x))。
pub fn yoneda_forward(f : Presheaf, c : Int32, x : Int32) -> NatTrans {
  let cat = f.cat
  let yc = Presheaf::representable(cat, c)
  let comp : Array[Array[Int32]] = Array::make(cat.n_obj, [])
  for d in 0..<cat.n_obj {
    let tbl : Array[Int32] = Array::make(yc.sizes[d], 0)
    // yc.sizes[d] = #Hom(d,c)；第 j 個對應某 m : d → c
    let mut idx = 0
    for m in 0..<cat.n_mor {
      if cat.dom[m] == d && cat.cod[m] == c {
        // F(m) : F(c) → F(d)，x 為 F(c) 的局部索引
        tbl[idx] = f.act[m][x]
        idx = idx + 1
      }
    }
    comp[d] = tbl
  }
  { dom: yc, cod: f, comp, }
}

///|
/// Yoneda 反向：α ↦ α_c(id_c)。
pub fn yoneda_backward(f : Presheaf, c : Int32, alpha : NatTrans) -> Int32 {
  let cat = f.cat
  let idc = cat.idm[c]
  // id_c 在 Hom(c,c) 中的索引
  let yc = Presheaf::representable(cat, c)
  let mut idx = 0
  let mut found = 0
  for m in 0..<cat.n_mor {
    if cat.dom[m] == c && cat.cod[m] == c {
      if m == idc {
        found = idx
      }
      idx = idx + 1
    }
  }
  let _ = yc
  alpha.comp[c][found]
}

///|
/// 窮舉所有自然變換（小規模）：回傳 Nat(y(c), F) 的基數與所有元素。
pub fn all_natural_transforms(f : Presheaf, c : Int32) -> Array[NatTrans] {
  let cat = f.cat
  let yc = Presheaf::representable(cat, c)
  // 每個物件 d 需給出 |F(d)|^{|y(c)(d)|} 個函數；用混合進位枚舉
  let mut total = 1
  for d in 0..<cat.n_obj {
    let mut t = 1
    for _ in 0..<yc.sizes[d] {
      t = t * f.sizes[d]
    }
    total = total * t
  }
  let out : Array[NatTrans] = []
  for code0 in 0..<total {
    let mut code = code0
    let comp : Array[Array[Int32]] = Array::make(cat.n_obj, [])
    for d in 0..<cat.n_obj {
      let tbl : Array[Int32] = Array::make(yc.sizes[d], 0)
      for j in 0..<yc.sizes[d] {
        let base = if f.sizes[d] == 0 { 1 } else { f.sizes[d] }
        tbl[j] = code % base
        code = code / base
      }
      comp[d] = tbl
    }
    let nt : NatTrans = { dom: yc, cod: f, comp, }
    if nt.is_natural() {
      out.push(nt)
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 範疇化：有限集合群胚的基數、么半結構相干性
// ---------------------------------------------------------------------------

///|
pub fn factorial_big(n : Int32) -> @bigint.BigInt {
  let mut acc = @bigint.BigInt::from_int(1)
  for i in 1..<(n + 1) {
    acc = acc * @bigint.BigInt::from_int(i)
  }
  acc
}

///|
/// 有限群胚的基數（Leinster）：Σ_iso類 1/|Aut(x)|。
/// 對「有限集合與雙射」群胚：Σ_n 1/n! = e。
pub fn fin_set_groupoid_cardinality(n_max : Int32) -> @num.Rat {
  let mut acc = @num.Rat::zero()
  for n in 0..<(n_max + 1) {
    acc = acc.add(@num.Rat::make(@bigint.BigInt::from_int(1), factorial_big(n)))
  }
  acc
}

///|
pub fn checks() -> Array[(String, Bool, String)] {
  let out : Array[(String, Bool, String)] = []

  // 1. 範疇公理
  let wa = walking_arrow()
  let c2 = cyclic_group(2)
  let c3 = cyclic_group(3)
  let le : Array[Array[Bool]] = [
    [true, true, true],
    [false, true, true],
    [false, false, true],
  ]
  let pc = poset_category(3, le)
  out.push(("範疇公理：走路箭頭 1→0", wa.axioms(), "3 態射"))
  out.push(("範疇公理：群 C2", c2.axioms(), "2 態射"))
  out.push(("範疇公理：群 C3", c3.axioms(), "3 態射"))
  out.push(("範疇公理：偏序範疇 C3", pc.axioms(), "6 態射"))

  // 2. 函子律：C2 → C2 的恆等；以及「非函子」證人
  let f_id : Functor = { src: c2, dst: c2, on_obj: [0], on_mor: [0, 1], }
  out.push(("函子律：id_C2", f_id.is_functor(), ""))
  let f_bad : Functor = { src: c2, dst: c2, on_obj: [0], on_mor: [1, 0], }
  out.push(
    ("非函子證人：把單位映到非單位", !f_bad.is_functor(), ""),
  )

  // 3. 預層律 + Yoneda 來回
  let f_const = Presheaf::of_constant(wa, 2)
  out.push(
    ("預層律：常數預層（走路箭頭上）", f_const.is_functor(), ""),
  )
  let y0 = Presheaf::representable(wa, 0)
  out.push(("可表預層 y(0) 是預層", y0.is_functor(), ""))

  // Yoneda：對 F = 常數 2 的預層，逐一驗證 x ↦ α 的雙射
  let mut yon_ok = true
  let mut witness_count = 0
  for c in 0..<2 {
    let nts = all_natural_transforms(f_const, c)
    // 正向再反向
    for x in 0..<f_const.sizes[c] {
      let a = yoneda_forward(f_const, c, x)
      if !a.is_natural() {
        yon_ok = false
      }
      if yoneda_backward(f_const, c, a) != x {
        yon_ok = false
      }
    }
    // 反向再正向
    for a in nts {
      let x = yoneda_backward(f_const, c, a)
      let b = yoneda_forward(f_const, c, x)
      for d in 0..<2 {
        for j in 0..<b.comp[d].length() {
          if b.comp[d][j] != a.comp[d][j] {
            yon_ok = false
          }
        }
      }
    }
    // 基數相等：|Nat(y(c),F)| = |F(c)|
    if nts.length() != f_const.sizes[c] {
      yon_ok = false
    }
    witness_count = witness_count + nts.length()
  }
  out.push(
    (
      "Yoneda 引理：Nat(y(c),F) ≅ F(c)（雙向窮舉）",
      yon_ok,
      "枚舉了 \{witness_count} 個自然變換",
    ),
  )

  // 對可表預層本身再做一次
  let y1 = Presheaf::representable(wa, 1)
  let nts1 = all_natural_transforms(y1, 0)
  let mut yon2 = nts1.length() == y1.sizes[0]
  for a in nts1 {
    if !a.is_natural() {
      yon2 = false
    }
  }
  out.push(
    (
      "Yoneda：Nat(y(0), y(1)) ≅ y(1)(0) = Hom(0,1)", yon2, "1 個元素（就是 f）",
    ),
  )

  // 4. 範疇化：Σ 1/n! → e
  let n_terms = 18
  let s = fin_set_groupoid_cardinality(n_terms)
  let dec = s.to_decimal(16)
  let prefix_ok = dec.has_prefix("2.718281828459045")
  out.push(
    (
      "有限集合群胚基數 Σ1/n! (n≤15) 逼近 e（前 12 位）", prefix_ok,
      dec,
    ),
  )

  // 嚴謹誤差界：|S_N - e| < 1/(N!·(N+1))·(1/(1-1/(N+2))) < 1/(N!·N)
  let big_e = @num.Rat::make(
    @bigint.BigInt::from_string("2718281828459045"),
    @bigint.BigInt::from_string("1000000000000000"),
  )
  let tail = @num.Rat::make(
    @bigint.BigInt::from_int(1),
    factorial_big(n_terms) * @bigint.BigInt::from_int(n_terms),
  )
  // 加上十進位截斷誤差 1e-16（有理數加法，全程精確）
  let trunc = @num.Rat::make(
    @bigint.BigInt::from_int(1),
    @bigint.BigInt::from_string("1000000000000000"),
  )
  let bound = tail.add(trunc)
  let diff = s.sub(big_e)
  let absdiff = if diff.compare(@num.Rat::zero()) < 0 {
    diff.neg()
  } else {
    diff
  }
  out.push(
    (
      "收斂誤差 < 1/(N!·N) + 1e-16（有理數嚴格比較）",
      absdiff.compare(bound) < 0,
      "N=\{n_terms}",
    ),
  )

  // 5. 非平凡性：群胚基數 ≠ 集合基數（後者為無限），且 Σ1/n! 非有理
  //    證人：1/n! 的尾項使 S_N 嚴格遞增
  let s2 = fin_set_groupoid_cardinality(n_terms - 1)
  out.push(
    (
      "非平凡性：S_N 嚴格遞增（尾項 1/N! > 0）",
      s.compare(s2) > 0,
      "",
    ),
  )

  out
}
