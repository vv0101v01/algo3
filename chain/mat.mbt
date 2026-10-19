// ============================================================================
// chain/mat — Q 上精確線性代數：rref、秩、核/餘核基底、誘導映射、蛇引理 (snake
//             lemma) 的「計算式」驗證。
//
// 蛇引理的六個位置全部以「秩條件 + 合成為零」實證，並以隨機精確有理數測 200 例。
// ============================================================================

///|
pub type Row = Array[@num.Rat]

///|
pub type RatMat = Array[Row]

///|
pub(all) struct Mat {
  r : Int32
  c : Int32
  d : RatMat
}

///|
pub fn Mat::zero(r : Int32, c : Int32) -> Mat {
  let d : RatMat = []
  for _ in 0..<r {
    let row : Array[@num.Rat] = []
    for _ in 0..<c {
      row.push(@num.Rat::zero())
    }
    d.push(row)
  }
  { r, c, d, }
}

///|
pub fn Mat::of(rows : RatMat) -> Mat {
  let r = rows.length()
  let c = if r == 0 { 0 } else { rows[0].length() }
  { r, c, d: rows, }
}

///|
pub fn Mat::id(n : Int32) -> Mat {
  let m = Mat::zero(n, n)
  for i in 0..<n {
    m.d[i][i] = @num.Rat::one()
  }
  m
}

///|
pub fn Mat::get(self : Mat, i : Int32, j : Int32) -> @num.Rat {
  self.d[i][j]
}

///|
pub fn Mat::mul(self : Mat, o : Mat) -> Mat {
  let out = Mat::zero(self.r, o.c)
  for i in 0..<self.r {
    for k in 0..<self.c {
      let a = self.d[i][k]
      if a.is_zero() {
        continue
      }
      for j in 0..<o.c {
        out.d[i][j] = out.d[i][j].add(a.mul(o.d[k][j]))
      }
    }
  }
  out
}

///|
pub fn Mat::add(self : Mat, o : Mat) -> Mat {
  let out = Mat::zero(self.r, self.c)
  for i in 0..<self.r {
    for j in 0..<self.c {
      out.d[i][j] = self.d[i][j].add(o.d[i][j])
    }
  }
  out
}

///|
pub fn Mat::neg(self : Mat) -> Mat {
  let out = Mat::zero(self.r, self.c)
  for i in 0..<self.r {
    for j in 0..<self.c {
      out.d[i][j] = self.d[i][j].neg()
    }
  }
  out
}

///|
pub fn Mat::sub(self : Mat, o : Mat) -> Mat {
  self.add(o.neg())
}

///|
pub fn Mat::is_zero(self : Mat) -> Bool {
  for i in 0..<self.r {
    for j in 0..<self.c {
      if !self.d[i][j].is_zero() {
        return false
      }
    }
  }
  true
}

///|
pub fn Mat::eq(self : Mat, o : Mat) -> Bool {
  if self.r != o.r || self.c != o.c {
    return false
  }
  for i in 0..<self.r {
    for j in 0..<self.c {
      if self.d[i][j] != o.d[i][j] {
        return false
      }
    }
  }
  true
}

///|
/// 轉置
pub fn Mat::transpose(self : Mat) -> Mat {
  let out = Mat::zero(self.c, self.r)
  for i in 0..<self.r {
    for j in 0..<self.c {
      out.d[j][i] = self.d[i][j]
    }
  }
  out
}

///|
/// 簡化行梯陣（RREF），並回傳樞軸列索引。
pub fn Mat::rref(self : Mat) -> (Mat, Array[Int32]) {
  let out = Mat::zero(self.r, self.c)
  for i in 0..<self.r {
    for j in 0..<self.c {
      out.d[i][j] = self.d[i][j]
    }
  }
  let piv : Array[Int32] = []
  let mut row = 0
  for col in 0..<self.c {
    if row >= self.r {
      break
    }
    let mut p = -1
    for r0 in row..<self.r {
      if p < 0 && !out.d[r0][col].is_zero() {
        p = r0
      }
    }
    if p < 0 {
      continue
    }
    // 交換
    for j in 0..<self.c {
      let t = out.d[row][j]
      out.d[row][j] = out.d[p][j]
      out.d[p][j] = t
    }
    let inv = @num.Rat::one().div(out.d[row][col])
    for j in 0..<self.c {
      out.d[row][j] = out.d[row][j].mul(inv)
    }
    for r0 in 0..<self.r {
      if r0 != row && !out.d[r0][col].is_zero() {
        let f = out.d[r0][col]
        for j in 0..<self.c {
          out.d[r0][j] = out.d[r0][j].sub(f.mul(out.d[row][j]))
        }
      }
    }
    piv.push(col)
    row = row + 1
  }
  (out, piv)
}

///|
pub fn Mat::rank(self : Mat) -> Int32 {
  let (_, piv) = self.rref()
  piv.length()
}

///|
/// 核基底：{x : M x = 0}，回傳一組線性獨立的向量（每個長度 = c）。
pub fn Mat::ker_basis(self : Mat) -> Array[Row] {
  let (rr, piv) = self.rref()
  let out : Array[Row] = []
  for j in 0..<self.c {
    let mut is_piv = false
    for p in piv {
      if p == j {
        is_piv = true
      }
    }
    if is_piv {
      continue
    }
    let v : Array[@num.Rat] = []
    for _ in 0..<self.c {
      v.push(@num.Rat::zero())
    }
    v[j] = @num.Rat::one()
    for i in 0..<piv.length() {
      v[piv[i]] = rr.d[i][j].neg()
    }
    out.push(v)
  }
  out
}

///|
/// 行空間基底（RREF 的樞軸行取原矩陣的列 → 這裡回傳「行向量」在 Q^r 中）。
pub fn Mat::col_basis(self : Mat) -> Array[Row] {
  let (_, piv) = self.rref()
  let out : Array[Row] = []
  for p in piv {
    let v : Array[@num.Rat] = []
    for i in 0..<self.r {
      v.push(self.d[i][p])
    }
    out.push(v)
  }
  out
}

///|
/// 在 span(basis) 中求 y 的座標（basis 向量線性獨立）；無解回 None。
pub fn solve_coords(
  basis : Array[Row],
  y : Array[@num.Rat],
) -> Array[@num.Rat]? {
  let k = basis.length()
  let n = y.length()
  if k == 0 {
    for v in y {
      if !v.is_zero() {
        return None
      }
    }
    return Some([])
  }
  // 方程 basis * c = y，未知數 k
  let rows : Array[Row] = []
  for i in 0..<n {
    let row : Array[@num.Rat] = []
    for j in 0..<k {
      row.push(basis[j][i])
    }
    row.push(y[i])
    rows.push(row)
  }
  let m = Mat::of(rows)
  let (rr, piv) = m.rref()
  // 檢查相容性：若某列係數全零但右端非零 → 無解
  for i in 0..<m.r {
    let mut all_zero = true
    for j in 0..<k {
      if !rr.d[i][j].is_zero() {
        all_zero = false
      }
    }
    if all_zero && !rr.d[i][k].is_zero() {
      return None
    }
  }
  let sol : Array[@num.Rat] = []
  for _ in 0..<k {
    sol.push(@num.Rat::zero())
  }
  for i in 0..<piv.length() {
    if piv[i] < k {
      sol[piv[i]] = rr.d[i][k]
    }
  }
  Some(sol)
}

///|
/// 解 M x = y 的一組解（自由變數取 0）；無解回 None。
pub fn solve_linear(m : Mat, y : Array[@num.Rat]) -> Array[@num.Rat]? {
  let rows : Array[Row] = []
  for i in 0..<m.r {
    let row : Array[@num.Rat] = []
    for j in 0..<m.c {
      row.push(m.d[i][j])
    }
    row.push(y[i])
    rows.push(row)
  }
  let aug = Mat::of(rows)
  let (rr, piv) = aug.rref()
  for i in 0..<aug.r {
    let mut all_zero = true
    for j in 0..<m.c {
      if !rr.d[i][j].is_zero() {
        all_zero = false
      }
    }
    if all_zero && !rr.d[i][m.c].is_zero() {
      return None
    }
  }
  let sol : Array[@num.Rat] = []
  for _ in 0..<m.c {
    sol.push(@num.Rat::zero())
  }
  for i in 0..<piv.length() {
    if piv[i] < m.c {
      sol[piv[i]] = rr.d[i][m.c]
    }
  }
  Some(sol)
}

///|
/// 由向量組造矩陣（行 = basis）。
pub fn mat_of_cols(basis : Array[Row], n : Int32) -> Mat {
  let m = Mat::zero(n, basis.length())
  for j in 0..<basis.length() {
    for i in 0..<n {
      m.d[i][j] = basis[j][i]
    }
  }
  m
}

///|
/// 擴大基底：把 span(basis) 補成 Q^n 的一組基底（用標準基底向量逐一嘗試）。
pub fn complement_basis(basis : Array[Row], n : Int32) -> Array[Row] {
  let cur : Array[Row] = basis.copy()
  let out : Array[Row] = []
  for j in 0..<n {
    let e : Array[@num.Rat] = []
    for i in 0..<n {
      e.push(if i == j { @num.Rat::one() } else { @num.Rat::zero() })
    }
    let cand : Array[Row] = cur.copy()
    cand.push(e)
    if mat_of_cols(cand, n).rank() > mat_of_cols(cur, n).rank() {
      cur.push(e)
      out.push(e)
    }
  }
  out
}

///|
/// 誘導映射：φ (r×n) 限制在 span(from)，像落在 span(to)，回傳 to-座標下的矩陣。
pub fn induce(phi : Mat, from : Array[Row], to : Array[Row]) -> Mat {
  let out = Mat::zero(to.length(), from.length())
  for j in 0..<from.length() {
    // w = phi * from[j]
    let w : Array[@num.Rat] = []
    for i in 0..<phi.r {
      let mut s = @num.Rat::zero()
      for k in 0..<phi.c {
        s = s.add(phi.d[i][k].mul(from[j][k]))
      }
      w.push(s)
    }
    match solve_coords(to, w) {
      Some(cs) =>
        for i in 0..<cs.length() {
          out.d[i][j] = cs[i]
        }
      None => abort("induce: image not in target span")
    }
  }
  out
}

///|
/// 模掉 mod_basis 後的座標：y ≡ Σ c_j basis_j (mod span(mod_basis))。
pub fn coords_mod(
  y : Array[@num.Rat],
  basis : Array[Row],
  mbasis : Array[Row],
) -> Array[@num.Rat] {
  let all : Array[Row] = []
  for v in basis {
    all.push(v)
  }
  for v in mbasis {
    all.push(v)
  }
  match solve_coords(all, y) {
    Some(cs) => {
      let out : Array[@num.Rat] = []
      for i in 0..<basis.length() {
        out.push(cs[i])
      }
      out
    }
    None => abort("coords_mod: not in span")
  }
}

// ---------------------------------------------------------------------------
// 蛇引理
// ---------------------------------------------------------------------------

///|
/// 蛇引理資料：兩列正合 0→A→B→C→0、0→A'→B'→C'→0，與交換方形。
pub(all) struct Snake {
  a : Mat // A → A'
  b : Mat // B → B'
  c : Mat // C → C'
  f : Mat // A → B
  g : Mat // B → C
  f2 : Mat // A' → B'
  g2 : Mat // B' → C'
}

///|
pub fn Snake::hypotheses(self : Snake) -> Bool {
  let nA = self.f.c
  let nB = self.f.r
  let nC = self.g.r
  let ok_shapes = self.a.c == nA &&
    self.a.r == self.f2.c &&
    self.b.c == nB &&
    self.b.r == self.f2.r &&
    self.c.c == nC &&
    self.c.r == self.g2.r &&
    self.g.c == nB &&
    self.g2.c == self.f2.r
  let inj = self.f.rank() == nA
  let surj = self.g.rank() == nC
  let mid = self.f.rank() + self.g.rank() == nB
  let inj2 = self.f2.rank() == self.f2.c
  let surj2 = self.g2.rank() == self.g2.r
  let mid2 = self.f2.rank() + self.g2.rank() == self.f2.r
  let sq1 = self.b.mul(self.f).eq(self.f2.mul(self.a))
  let sq2 = self.c.mul(self.g).eq(self.g2.mul(self.b))
  ok_shapes && inj && surj && mid && inj2 && surj2 && mid2 && sq1 && sq2
}

///|
/// 誘導映射（模掉 mod_target 後的座標）。
pub fn induce_mod(
  phi : Mat,
  from : Array[Row],
  to : Array[Row],
  mod_target : Array[Row],
) -> Mat {
  let out = Mat::zero(to.length(), from.length())
  for j in 0..<from.length() {
    let w : Array[@num.Rat] = []
    for i in 0..<phi.r {
      let mut s = @num.Rat::zero()
      for k in 0..<phi.c {
        s = s.add(phi.d[i][k].mul(from[j][k]))
      }
      w.push(s)
    }
    let cs = coords_mod(w, to, mod_target)
    for i in 0..<cs.length() {
      out.d[i][j] = cs[i]
    }
  }
  out
}

///|
/// 在六個位置逐一檢查正合性。
pub fn Snake::exact(self : Snake) -> Bool {
  let ker_a = self.a.ker_basis()
  let ker_b = self.b.ker_basis()
  let ker_c = self.c.ker_basis()
  let coker_a = complement_basis(self.a.col_basis(), self.a.r)
  let coker_b = complement_basis(self.b.col_basis(), self.b.r)
  let coker_c = complement_basis(self.c.col_basis(), self.c.r)
  let s1 = induce(self.f, ker_a, ker_b)
  let s2 = induce(self.g, ker_b, ker_c)
  let s4 = induce_mod(self.f2, coker_a, coker_b, self.b.col_basis())
  let s5 = induce_mod(self.g2, coker_b, coker_c, self.c.col_basis())
  // δ : ker c → coker a
  let delta = Mat::zero(coker_a.length(), ker_c.length())
  for j in 0..<ker_c.length() {
    let x = ker_c[j]
    // 提升：解 g y = x
    let y = match solve_linear(self.g, x) {
      Some(y) => y
      None => return false
    }
    // b y ∈ ker g'；解 f' z = b y
    let by : Array[@num.Rat] = []
    for i in 0..<self.b.r {
      let mut s = @num.Rat::zero()
      for k in 0..<self.b.c {
        s = s.add(self.b.d[i][k].mul(y[k]))
      }
      by.push(s)
    }
    let z = match solve_linear(self.f2, by) {
      Some(z) => z
      None => return false
    }
    let cs = coords_mod(z, coker_a, self.a.col_basis())
    for i in 0..<cs.length() {
      delta.d[i][j] = cs[i]
    }
  }
  let dim_ka = ker_a.length()
  let dim_kb = ker_b.length()
  let dim_kc = ker_c.length()
  let dim_ca = coker_a.length()
  let dim_cb = coker_b.length()
  let dim_cc = coker_c.length()
  // 各位置的「合成為零」
  let comp_ker_b = s2.mul(s1) // s2 ∘ s1
  let comp_ker_c = delta.mul(s2) // δ ∘ s2
  let comp_coker_a = s4.mul(delta) // s4 ∘ δ
  let comp_coker_b = s5.mul(s4) // s5 ∘ s4
  if !comp_ker_b.is_zero() ||
    !comp_ker_c.is_zero() ||
    !comp_coker_a.is_zero() ||
    !comp_coker_b.is_zero() {
    return false
  }
  // 秩條件 ⟺ 正合
  let ok1 = s1.rank() == dim_ka // ker a → ker b 單射
  let ok2 = s1.rank() + s2.rank() == dim_kb
  let ok3 = s2.rank() + delta.rank() == dim_kc
  let ok4 = delta.rank() + s4.rank() == dim_ca
  let ok5 = s4.rank() + s5.rank() == dim_cb
  let ok6 = s5.rank() == dim_cc // 滿射
  ok1 && ok2 && ok3 && ok4 && ok5 && ok6
}
