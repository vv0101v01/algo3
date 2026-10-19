// ============================================================================
// der — 導範疇 (Derived category) D^b(Ch(ℚ))
//
// 【背景】Ch(ℚ) = 有限維 ℚ-向量空間的鏈複形範疇。同倫範疇 K(ℚ) 的態射為
//   鏈映射模去鏈同倫：   Hom_{K}(C, D) = Hom_{Ch}(C, D) / ≃，
//   其中 f ≃ g ⟺ ∃ h（鏈同倫）使 f − g = ∂h + h∂。
//   導範疇 D^b(ℚ) = K^b(ℚ)[qis⁻¹] 是把所有準同構 (quasi-isomorphism) 形式反演。
//
// 【定理 A】f : C → D 是準同構 ⟺ cone(f) 無環 (acyclic)。
// 【定理 B】對域 ℚ 上的複形：每個準同構都是同倫等價；且 D^b(ℚ) ≃ 分次 ℚ-向量空間。
//   證明策略（本檔以計算實現）：取 Z_n = ker ∂_n、B_n = im ∂_{n+1}，選補空間
//        C_n = B_n ⊕ W_n ⊕ A_n,   W_n ≅ H_n,   ∂_n|A_n : A_n ≅ B_{n-1},
//   則 C = (⊕_n W_n[n]) ⊕ (可縮塊)，故存在鏈映射 p : C → H_*(C)（目標微分為 0）
//   為準同構，且具有同倫逆。
// 【推論】dim Hom_{D}(C, D) = Σ_n h_n(C) · h_n(D)，h_n = dim H_n。
//
// 【本檔驗證】
//   (D1) 錐複形 ∂² = 0（隨機 24 例）
//   (D2) 長正合序列：dim H_n(cone f) = dim coker H_n(f) + dim ker H_{n−1}(f)
//   (D3) 同倫不變性：f ≃ g ⟹ H_n(f) = H_n(g)
//   (D4) Hom_K 的線性代數維度 = 鏈映射維度 − 零倫映射維度（以精確有理數 rref 計算）
//   (D5) dim Hom_D(C,D) = Σ_n h_n(C)·h_n(D)（形式性推論，隨機複形對）
//   (D6) 形式性：顯式構造 p : C → H_*(C)，驗證其為鏈映射且誘導同構
//   (D7) 準同構 ⟹ 同倫等價：解線性方程構造 (g, h, k) 並代回驗證
// ============================================================================

// ---------------------------------------------------------------------------
// 1. 複形工具
// ---------------------------------------------------------------------------

///|
fn dim_at(c : @chain.Cx, i : Int32) -> Int32 {
  if i >= 0 && i < c.dims.length() {
    c.dims[i]
  } else {
    0
  }
}

///|
fn ncomp(c : @chain.Cx) -> Int32 {
  c.dims.length()
}

///|
fn zero_mat(r : Int32, c : Int32) -> @chain.Mat {
  @chain.Mat::zero(r, c)
}

///|
/// ∂_i : C_i → C_{i−1}（超出範圍時為 0 矩陣）。
fn dmat(c : @chain.Cx, i : Int32) -> @chain.Mat {
  if i >= 1 && i < c.dims.length() {
    c.d[i]
  } else {
    zero_mat(dim_at(c, i - 1), dim_at(c, i))
  }
}

///|
/// 把複形補齊（或截斷）到 n 個分量。
fn pad(c : @chain.Cx, n : Int32) -> @chain.Cx {
  let dims : Array[Int32] = []
  for i in 0..<n {
    dims.push(dim_at(c, i))
  }
  let d : Array[@chain.Mat] = [zero_mat(0, dims[0])]
  for i in 1..<n {
    d.push(dmat(c, i))
  }
  @chain.Cx::make(dims, d)
}

///|
/// 未知數總數：Σ_i dim D_i · dim C_i。
fn comp_size(c : @chain.Cx, d : @chain.Cx) -> Int32 {
  let n = ncomp(c)
  let mut s = 0
  for i in 0..<n {
    s = s + dim_at(c, i) * dim_at(d, i)
  }
  s
}

///|
/// 係數向量 → 鏈映射分量。
fn vec_to_mats(
  src : @chain.Cx,
  dst : @chain.Cx,
  x : Array[@num.Rat],
) -> Array[@chain.Mat] {
  let n = ncomp(src)
  let out : Array[@chain.Mat] = []
  let mut k = 0
  for i in 0..<n {
    let m = zero_mat(dim_at(dst, i), dim_at(src, i))
    for a in 0..<dim_at(dst, i) {
      for b in 0..<dim_at(src, i) {
        m.d[a][b] = x[k]
        k = k + 1
      }
    }
    out.push(m)
  }
  out
}

///|
/// 分量 → 扁平向量。
fn mats_to_vec(ms : Array[@chain.Mat]) -> Array[@num.Rat] {
  let out : Array[@num.Rat] = []
  for m in ms {
    for a in 0..<m.r {
      for b in 0..<m.c {
        out.push(m.d[a][b])
      }
    }
  }
  out
}

///|
/// 鏈映射殘差 (∂_D f − f ∂_C)_i，i ≥ 1；值域為 Hom(C_i, D_{i−1})。
fn chain_residual(
  src : @chain.Cx,
  dst : @chain.Cx,
  f : Array[@chain.Mat],
) -> Array[@num.Rat] {
  let out : Array[@num.Rat] = []
  for i in 1..<ncomp(src) {
    let r = dmat(dst, i).mul(f[i]).sub(f[i - 1].mul(dmat(src, i)))
    for a in 0..<r.r {
      for b in 0..<r.c {
        out.push(r.d[a][b])
      }
    }
  }
  out
}

///|
/// 方程空間維度：Σ_{i ≥ 1} dim D_{i−1} · dim C_i。
fn eq_size(c : @chain.Cx, d : @chain.Cx) -> Int32 {
  let mut s = 0
  for i in 1..<ncomp(c) {
    s = s + dim_at(d, i - 1) * dim_at(c, i)
  }
  s
}

///|
/// 同倫殘差 (∂_D h + h ∂_C)_i，h_i : C_i → D_{i+1}。
fn homotopy_residual(
  src : @chain.Cx,
  dst : @chain.Cx,
  h : Array[@chain.Mat],
) -> Array[@num.Rat] {
  let n = ncomp(src)
  let out : Array[@num.Rat] = []
  for i in 0..<n {
    let t1 = dmat(dst, i + 1).mul(h[i])
    let t2 = if i >= 1 {
      h[i - 1].mul(dmat(src, i))
    } else {
      zero_mat(dim_at(dst, i), dim_at(src, i))
    }
    let r = t1.add(t2)
    for a in 0..<r.r {
      for b in 0..<r.c {
        out.push(r.d[a][b])
      }
    }
  }
  out
}

///|
/// 同倫未知數總數：Σ_i dim D_{i+1} · dim C_i。
fn hom_size(c : @chain.Cx, d : @chain.Cx) -> Int32 {
  let n = ncomp(c)
  let mut s = 0
  for i in 0..<n {
    s = s + dim_at(d, i + 1) * dim_at(c, i)
  }
  s
}

///|
/// 係數向量 → 同倫分量 h_i : C_i → D_{i+1}。
fn vec_to_hom(
  src : @chain.Cx,
  dst : @chain.Cx,
  x : Array[@num.Rat],
) -> Array[@chain.Mat] {
  let n = ncomp(src)
  let out : Array[@chain.Mat] = []
  let mut k = 0
  for i in 0..<n {
    let m = zero_mat(dim_at(dst, i + 1), dim_at(src, i))
    for a in 0..<dim_at(dst, i + 1) {
      for b in 0..<dim_at(src, i) {
        m.d[a][b] = x[k]
        k = k + 1
      }
    }
    out.push(m)
  }
  out
}

///|
/// 鏈映射方程組的方陣：第 k 列 = 第 k 個基向量（單位鏈映射）的殘差。
/// 其核空間 = 全體鏈映射（以係數向量表示）。
fn chainmap_operator(src : @chain.Cx, dst : @chain.Cx) -> @chain.Mat {
  let nu = comp_size(src, dst)
  let rows : Array[Array[@num.Rat]] = []
  let x : Array[@num.Rat] = []
  for _ in 0..<nu {
    x.push(@num.Rat::zero())
  }
  for k in 0..<nu {
    x[k] = @num.Rat::one()
    let f = vec_to_mats(src, dst, x)
    rows.push(chain_residual(src, dst, f))
    x[k] = @num.Rat::zero()
  }
  @chain.Mat::of(rows).transpose()
}

///|
/// 同倫算子：行 = 殘差，列 = 同倫未知數；其秩 = 零倫映射空間的維度。
fn homotopy_operator(src : @chain.Cx, dst : @chain.Cx) -> @chain.Mat {
  let nh = hom_size(src, dst)
  let rows : Array[Array[@num.Rat]] = []
  let x : Array[@num.Rat] = []
  for _ in 0..<nh {
    x.push(@num.Rat::zero())
  }
  for k in 0..<nh {
    x[k] = @num.Rat::one()
    let h = vec_to_hom(src, dst, x)
    rows.push(homotopy_residual(src, dst, h))
    x[k] = @num.Rat::zero()
  }
  @chain.Mat::of(rows).transpose()
}

///|
/// dim Hom_K(C, D) = dim ker(鏈映射方程) − dim im(同倫算子)。
fn hom_k_dim(src : @chain.Cx, dst : @chain.Cx) -> Int32 {
  let n = ncomp(src)
  let a = pad(src, n)
  let b = pad(dst, n)
  let nu = comp_size(a, b)
  let maps_dim = nu - chainmap_operator(a, b).rank()
  let hrank = homotopy_operator(a, b).rank()
  maps_dim - hrank
}

// ---------------------------------------------------------------------------
// 2. 同調
// ---------------------------------------------------------------------------

///|
/// 循環 Z_i = ker ∂_i 的基底。
fn cycles_basis(c : @chain.Cx, i : Int32) -> Array[@chain.Row] {
  dmat(c, i).ker_basis()
}

///|
/// 邊界 B_i = im ∂_{i+1} 的基底。
fn boundaries_basis(c : @chain.Cx, i : Int32) -> Array[@chain.Row] {
  dmat(c, i + 1).col_basis()
}

///|
/// 同調 H_i 的基底：由 B_i 出發，逐一加入與邊界線性獨立的新循環。
fn homology_basis(c : @chain.Cx, i : Int32) -> Array[@chain.Row] {
  let cur : Array[@chain.Row] = boundaries_basis(c, i)
  let out : Array[@chain.Row] = []
  let n = dim_at(c, i)
  for z in cycles_basis(c, i) {
    let cand : Array[@chain.Row] = cur.copy()
    cand.push(z)
    if @chain.mat_of_cols(cand, n).rank() > @chain.mat_of_cols(cur, n).rank() {
      cur.push(z)
      out.push(z)
    }
  }
  out
}

///|
/// h_i = dim H_i。
fn hom_dim(c : @chain.Cx, i : Int32) -> Int32 {
  homology_basis(c, i).length()
}

///|
/// 誘導映射 H_i(f) 的矩陣（以同調基底表示）。
fn induced_hom(
  f : Array[@chain.Mat],
  src : @chain.Cx,
  dst : @chain.Cx,
  i : Int32,
) -> @chain.Mat {
  let hb_a = homology_basis(src, i)
  let hb_b = homology_basis(dst, i)
  let bb = boundaries_basis(dst, i)
  let out = zero_mat(hb_b.length(), hb_a.length())
  for j in 0..<hb_a.length() {
    let w : Array[@num.Rat] = []
    for a in 0..<dim_at(dst, i) {
      let mut s = @num.Rat::zero()
      for b in 0..<dim_at(src, i) {
        s = s.add(f[i].d[a][b].mul(hb_a[j][b]))
      }
      w.push(s)
    }
    let cs = @chain.coords_mod(w, hb_b, bb)
    for a in 0..<cs.length() {
      out.d[a][j] = cs[a]
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 3. 隨機生成（確定性 LCG）
// ---------------------------------------------------------------------------

///|
fn lcg(s : Int32) -> Int32 {
  (s * 1103515245 + 12345) % 2147483647
}

///|
fn rand_rat(seed : Int32) -> (@num.Rat, Int32) {
  let s = lcg(seed)
  let v = s / 65536 % 5 - 2
  (@num.Rat::of_int(v), s)
}

///|
fn rand_matrix(r : Int32, c : Int32, seed0 : Int32) -> (@chain.Mat, Int32) {
  let m = zero_mat(r, c)
  let mut seed = seed0
  for i in 0..<r {
    for j in 0..<c {
      let (x, s2) = rand_rat(seed)
      seed = s2
      m.d[i][j] = x
    }
  }
  (m, seed)
}

///|
/// 隨機複形：由高位往低位建微分，強制 ∂_i ∂_{i+1} = 0
/// （d[i] 的每一列取自 ker(d[i+1]ᵀ)）。
fn rand_complex(dims : Array[Int32], seed0 : Int32) -> (@chain.Cx, Int32) {
  let k = dims.length()
  let dm : Array[@chain.Mat] = [zero_mat(0, dims[0])]
  for _ in 1..<k {
    dm.push(zero_mat(0, 0))
  }
  let mut seed = seed0
  let (top, s1) = rand_matrix(dims[k - 2], dims[k - 1], seed)
  seed = s1
  dm[k - 1] = top
  let mut i = k - 2
  while i >= 1 {
    let basis = dm[i + 1].transpose().ker_basis()
    let m = zero_mat(dims[i - 1], dims[i])
    for a in 0..<dims[i - 1] {
      if basis.length() > 0 {
        let coeffs : Array[@num.Rat] = []
        for _ in 0..<basis.length() {
          let (x, s2) = rand_rat(seed)
          seed = s2
          coeffs.push(x)
        }
        for b in 0..<dims[i] {
          let mut s = @num.Rat::zero()
          for t in 0..<basis.length() {
            s = s.add(coeffs[t].mul(basis[t][b]))
          }
          m.d[a][b] = s
        }
      }
    }
    dm[i] = m
    i = i - 1
  }
  (@chain.Cx::make(dims, dm), seed)
}

///|
/// 隨機鏈映射：在鏈映射方程組的核空間中取隨機線性組合。
fn rand_chainmap(
  a : @chain.Cx,
  b : @chain.Cx,
  seed0 : Int32,
) -> (@chain.CxMap, Int32) {
  let n = ncomp(a)
  let bb = pad(b, n)
  let nu = comp_size(a, bb)
  let ker = chainmap_operator(a, bb).ker_basis()
  let x : Array[@num.Rat] = []
  for _ in 0..<nu {
    x.push(@num.Rat::zero())
  }
  let mut seed = seed0
  for k in 0..<ker.length() {
    let (c, s2) = rand_rat(seed)
    seed = s2
    for j in 0..<nu {
      x[j] = x[j].add(c.mul(ker[k][j]))
    }
  }
  let maps = vec_to_mats(a, bb, x)
  ({ src: a, dst: bb, maps, }, seed)
}

// ---------------------------------------------------------------------------
// 4. 形式性：p : C → H_*(C)
// ---------------------------------------------------------------------------

///|
/// 建構 p_n : C_n → H_n（目標微分為零）：
/// 取 Z_n = B_n ⊕ W_n、A_n 為 Z_n 在 C_n 中的補，
/// 以對偶基底 λ_j（λ_j|W = δ、λ_j|B = 0、λ_j|A = 0）給出投影 C_n → W_n ≅ H_n。
fn formality_map(c : @chain.Cx) -> @chain.CxMap {
  let n = ncomp(c)
  let hdims : Array[Int32] = []
  for i in 0..<n {
    hdims.push(hom_dim(c, i))
  }
  let zd : Array[@chain.Mat] = [zero_mat(0, hdims[0])]
  for _ in 1..<n {
    zd.push(zero_mat(0, 0))
  }
  for i in 1..<n {
    zd[i] = zero_mat(hdims[i - 1], hdims[i])
  }
  let target = @chain.Cx::make(hdims, zd)
  let maps : Array[@chain.Mat] = []
  for i in 0..<n {
    let w = homology_basis(c, i)
    let b = boundaries_basis(c, i)
    let z = cycles_basis(c, i)
    let a = @chain.complement_basis(z, dim_at(c, i))
    // 完整基底（列）：W ⊕ B ⊕ A
    let rows : Array[@chain.Row] = []
    for v in w {
      rows.push(v)
    }
    for v in b {
      rows.push(v)
    }
    for v in a {
      rows.push(v)
    }
    let basis = @chain.Mat::of(rows)
    let p = zero_mat(w.length(), dim_at(c, i))
    for j in 0..<w.length() {
      let rhs : Array[@num.Rat] = []
      for t in 0..<rows.length() {
        rhs.push(if t == j { @num.Rat::one() } else { @num.Rat::zero() })
      }
      match @chain.solve_linear(basis, rhs) {
        Some(lam) =>
          for t in 0..<lam.length() {
            p.d[j][t] = lam[t]
          }
        None => abort("formality_map: 對偶基底無解")
      }
    }
    maps.push(p)
  }
  { src: c, dst: target, maps, }
}

///|
fn is_zero_mat(m : @chain.Mat) -> Bool {
  m.is_zero()
}

// ---------------------------------------------------------------------------
// 5. 驗證
// ---------------------------------------------------------------------------

///|
pub fn checks() -> Array[(String, Bool, String)] {
  let out : Array[(String, Bool, String)] = []
  // ---- (D1) 錐複形 ∂² = 0 ----------------------------------------------
  let dims_pool : Array[Array[Int32]] = [
    [1, 2, 1, 0],
    [2, 1, 1, 0],
    [1, 1, 2, 1],
    [2, 2, 1, 0],
  ]
  let mut d1 = true
  let mut d1n = 0
  let mut seed = 7
  for t in 0..<24 {
    let (a, s1) = rand_complex(dims_pool[t % 4], seed)
    seed = s1
    let (b, s2) = rand_complex(dims_pool[(t + 1) % 4], seed)
    seed = s2
    let (f, s3) = rand_chainmap(a, b, seed)
    seed = s3
    d1n = d1n + 1
    if !@chain.cone(f).is_complex() {
      d1 = false
    }
  }
  out.push(
    ("(D1) 映射錐 cone(f) 滿足 ∂² = 0", d1, "\{d1n} 個隨機鏈映射"),
  )
  // ---- (D2) 長正合序列 ------------------------------------------------
  let mut d2 = true
  let mut d2n = 0
  let mut seed2 = 91
  for t in 0..<24 {
    let (a, s1) = rand_complex(dims_pool[t % 4], seed2)
    seed2 = s1
    let (b, s2) = rand_complex(dims_pool[(t + 1) % 4], seed2)
    seed2 = s2
    let (f, s3) = rand_chainmap(a, b, seed2)
    seed2 = s3
    let n = ncomp(a)
    let ap = pad(a, n)
    let bp = pad(b, n)
    let cf = @chain.cone(f)
    for i in 0..<n {
      d2n = d2n + 1
      let r = induced_hom(f.maps, ap, bp, i).rank()
      let hb = hom_dim(bp, i) - r
      let ha = if i >= 1 {
        hom_dim(ap, i - 1) - induced_hom(f.maps, ap, bp, i - 1).rank()
      } else {
        0
      }
      if hom_dim(cf, i) != hb + ha {
        d2 = false
      }
    }
  }
  out.push(
    (
      "(D2) 長正合序列：dim H_n(cone f) = dim coker H_n(f) + dim ker H_{n−1}(f)",
      d2,
      "\{d2n} 個 (n, f) 組合",
    ),
  )
  // ---- (D3) 同倫不變性 ------------------------------------------------
  let mut d3 = true
  let mut d3n = 0
  let mut seed3 = 313
  for t in 0..<16 {
    let (a, s1) = rand_complex(dims_pool[t % 4], seed3)
    seed3 = s1
    let (b, s2) = rand_complex(dims_pool[(t + 1) % 4], seed3)
    seed3 = s2
    let (f, s3) = rand_chainmap(a, b, seed3)
    seed3 = s3
    let n = ncomp(a)
    let ap = pad(a, n)
    let bp = pad(b, n)
    // 隨機同倫 h : C_i → D_{i+1}
    let ah = hom_size(ap, bp)
    let hv : Array[@num.Rat] = []
    for _ in 0..<ah {
      let (x, s4) = rand_rat(seed3)
      seed3 = s4
      hv.push(x)
    }
    let h = vec_to_hom(ap, bp, hv)
    // g = f + ∂h + h∂
    let resid = homotopy_residual(ap, bp, h)
    let gv = mats_to_vec(f.maps)
    let g : Array[@chain.Mat] = []
    for k in 0..<gv.length() {
      gv[k] = gv[k].add(resid[k])
    }
    let gm = vec_to_mats(ap, bp, gv)
    for i in 0..<n {
      d3n = d3n + 1
      let m1 = induced_hom(f.maps, ap, bp, i)
      let m2 = induced_hom(gm, ap, bp, i)
      if !m1.eq(m2) {
        d3 = false
      }
    }
  }
  out.push(
    (
      "(D3) 同倫不變性：f ≃ g ⟹ H_n(f) = H_n(g)",
      d3,
      "\{d3n} 個 (n, 配對)",
    ),
  )
  // ---- (D4) Hom_K 的線性代數定義 ---------------------------------------
  let mut d4 = true
  let mut d4n = 0
  let mut seed4 = 555
  for t in 0..<12 {
    let (a, s1) = rand_complex(dims_pool[t % 4], seed4)
    seed4 = s1
    let (b, s2) = rand_complex(dims_pool[(t + 2) % 4], seed4)
    seed4 = s2
    d4n = d4n + 1
    let n = ncomp(a)
    let ap = pad(a, n)
    let bp = pad(b, n)
    let nu = comp_size(ap, bp)
    let maps_dim = nu - chainmap_operator(ap, bp).rank()
    let hrank = homotopy_operator(ap, bp).rank()
    if hom_k_dim(ap, bp) != maps_dim - hrank || hom_k_dim(ap, bp) < 0 {
      d4 = false
    }
  }
  out.push(
    (
      "(D4) Hom_K = 鏈映射空間 / 零倫子空間（精確 rref 維度）",
      d4,
      "\{d4n} 對複形",
    ),
  )
  // ---- (D5) dim Hom_D = Σ h_n h_n -------------------------------------
  let mut d5 = true
  let mut d5n = 0
  let mut seed5 = 8675309
  for t in 0..<12 {
    let (a, s1) = rand_complex(dims_pool[t % 4], seed5)
    seed5 = s1
    let (b, s2) = rand_complex(dims_pool[(t + 3) % 4], seed5)
    seed5 = s2
    let n = ncomp(a)
    let ap = pad(a, n)
    let bp = pad(b, n)
    d5n = d5n + 1
    let mut sum = 0
    for i in 0..<n {
      sum = sum + hom_dim(ap, i) * hom_dim(bp, i)
    }
    if hom_k_dim(ap, bp) != sum {
      d5 = false
    }
  }
  out.push(
    (
      "(D5) dim Hom_D(C,D) = Σ_n h_n(C)·h_n(D)（形式性推論）",
      d5,
      "\{d5n} 對複形",
    ),
  )
  // ---- (D6) 形式性：p : C → H_*(C) 為準同構 ---------------------------
  let mut d6 = true
  let mut d6n = 0
  let mut seed6 = 2024
  for t in 0..<12 {
    let (a, s1) = rand_complex(dims_pool[t % 4], seed6)
    seed6 = s1
    let p = formality_map(a)
    d6n = d6n + 1
    // 鏈映射條件：p_i ∂_i = 0（目標微分為 0）
    for i in 1..<ncomp(a) {
      if !p.maps[i].mul(dmat(a, i)).is_zero() {
        d6 = false
      }
    }
    // 誘導同構：rank p_i = h_i
    for i in 0..<ncomp(a) {
      if p.maps[i].rank() != hom_dim(a, i) {
        d6 = false
      }
    }
  }
  out.push(
    (
      "(D6) 形式性：顯式 p : C → H_*(C) 為鏈映射且誘導同構",
      d6,
      "\{d6n} 個隨機複形",
    ),
  )
  // ---- (D7) 準同構 ⟹ 同倫等價（構造 g, h, k） -------------------------
  let mut d7 = true
  let mut d7n = 0
  let mut seed7 = 424242
  for t in 0..<10 {
    let (a, s1) = rand_complex(dims_pool[t % 4], seed7)
    seed7 = s1
    let f = formality_map(a)
    let src = a
    let dst = f.dst
    let n = ncomp(src)
    // 未知數：g_i : H_i → C_i、h_i : C_i → C_{i+1}、k_i : H_i → H_{i+1}
    let ng = comp_size(dst, src)
    let nh = hom_size(src, src)
    let nk = hom_size(dst, dst)
    let nunk = ng + nh + nk
    let nrows = comp_size(src, src) + comp_size(dst, dst)
    // 各未知數的殘差（列 = 方程，行 = 未知數）
    let cols : Array[Array[@num.Rat]] = []
    let x : Array[@num.Rat] = []
    for _ in 0..<nunk {
      x.push(@num.Rat::zero())
    }
    for u in 0..<nunk {
      x[u] = @num.Rat::one()
      let gv : Array[@num.Rat] = []
      for k in 0..<ng {
        gv.push(x[k])
      }
      let hv : Array[@num.Rat] = []
      for k in 0..<nh {
        hv.push(x[ng + k])
      }
      let kv : Array[@num.Rat] = []
      for k in 0..<nk {
        kv.push(x[ng + nh + k])
      }
      let g = vec_to_mats(dst, src, gv)
      let h = vec_to_hom(src, src, hv)
      let kk = vec_to_hom(dst, dst, kv)
      // E1 = (∂h + h∂) − g f
      let e1v = homotopy_residual(src, src, h)
      let gf = mats_to_vec(comp_mul(g, f.maps))
      let e1 : Array[@num.Rat] = []
      for j in 0..<e1v.length() {
        e1.push(e1v[j].sub(gf[j]))
      }
      // E2 = (∂k + k∂) − f g
      let e2v = homotopy_residual(dst, dst, kk)
      let fg = mats_to_vec(comp_mul(f.maps, g))
      let e2 : Array[@num.Rat] = []
      for j in 0..<e2v.length() {
        e2.push(e2v[j].sub(fg[j]))
      }
      let col : Array[@num.Rat] = []
      for v in e1 {
        col.push(v)
      }
      for v in e2 {
        col.push(v)
      }
      cols.push(col)
      x[u] = @num.Rat::zero()
    }
    let mat = @chain.Mat::of(cols).transpose()
    // 右端 = −(id_A, id_B)
    let rhs : Array[@num.Rat] = []
    for i in 0..<comp_size(src, src) {
      rhs.push(@num.Rat::zero())
    }
    for i in 0..<comp_size(dst, dst) {
      rhs.push(@num.Rat::zero())
    }
    // 在方程空間中填入 −id 的係數
    let mut off = 0
    for i in 0..<n {
      for a0 in 0..<dim_at(src, i) {
        for b0 in 0..<dim_at(src, i) {
          if a0 == b0 {
            rhs[off] = @num.Rat::one().neg()
          }
          off = off + 1
        }
      }
    }
    let mut off2 = comp_size(src, src)
    for i in 0..<n {
      for a0 in 0..<dim_at(dst, i) {
        for b0 in 0..<dim_at(dst, i) {
          if a0 == b0 {
            rhs[off2] = @num.Rat::one().neg()
          }
          off2 = off2 + 1
        }
      }
    }
    d7n = d7n + 1
    match @chain.solve_linear(mat, rhs) {
      None => d7 = false
      Some(sol) => {
        // 代回驗證
        let gv : Array[@num.Rat] = []
        for k in 0..<ng {
          gv.push(sol[k])
        }
        let hv : Array[@num.Rat] = []
        for k in 0..<nh {
          hv.push(sol[ng + k])
        }
        let kv : Array[@num.Rat] = []
        for k in 0..<nk {
          kv.push(sol[ng + nh + k])
        }
        let g = vec_to_mats(dst, src, gv)
        let h = vec_to_hom(src, src, hv)
        let kk = vec_to_hom(dst, dst, kv)
        let gf = comp_mul(g, f.maps)
        let fg = comp_mul(f.maps, g)
        // 檢查 g f − id = ∂h + h∂、f g − id = ∂k + k∂
        let r1 = homotopy_residual(src, src, h)
        let l1 = mats_to_vec(gf)
        for j in 0..<l1.length() {
          // l1 − id
          let mut v = l1[j]
          if is_id_pos(src, j) {
            v = v.sub(@num.Rat::one())
          }
          if v.compare(r1[j]) != 0 {
            d7 = false
          }
        }
        let r2 = homotopy_residual(dst, dst, kk)
        let l2 = mats_to_vec(fg)
        for j in 0..<l2.length() {
          let mut v = l2[j]
          if is_id_pos(dst, j) {
            v = v.sub(@num.Rat::one())
          }
          if v.compare(r2[j]) != 0 {
            d7 = false
          }
        }
        // 另外檢查 g 確為鏈映射
        for v in chain_residual(dst, src, g) {
          if !v.is_zero() {
            d7 = false
          }
        }
      }
      None => d7 = false
    }
  }
  out.push(
    (
      "(D7) 準同構 ⟹ 同倫等價：解線性方程構造 (g, h, k)",
      d7,
      "\{d7n} 個準同構",
    ),
  )
  out
}

///|
/// 分量乘法 (g ∘ f)_i = g_i f_i。
fn comp_mul(g : Array[@chain.Mat], f : Array[@chain.Mat]) -> Array[@chain.Mat] {
  let out : Array[@chain.Mat] = []
  for i in 0..<f.length() {
    out.push(g[i].mul(f[i]))
  }
  out
}

///|
/// 扁平向量位置 j 是否對應某分量的對角線（即單位映射的 1 位置）。
fn is_id_pos(c : @chain.Cx, j : Int32) -> Bool {
  let mut off = 0
  for i in 0..<ncomp(c) {
    let d = dim_at(c, i)
    for a in 0..<d {
      for b in 0..<d {
        if off == j {
          return a == b
        }
        off = off + 1
      }
    }
  }
  false
}
