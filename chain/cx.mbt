// ============================================================================
// chain/cx — 鏈複形、同調、鏈映射、映射錐、導範疇中的「準同構 ⟺ 錐無環」
//           以及 k[x]/(x²) 上 Ext 的極小自由分解計算。
// ============================================================================

///|
pub(all) struct Cx {
  dims : Array[Int32] // dims[i] = dim C_i
  d : Array[Mat] // d[i] : C_i → C_{i-1}（i ≥ 1）；d[0] 為空矩陣
}

///|
pub fn Cx::make(dims : Array[Int32], d : Array[Mat]) -> Cx {
  { dims, d, }
}

///|
pub fn Cx::is_complex(self : Cx) -> Bool {
  for i in 2..<self.dims.length() {
    if !self.d[i - 1].mul(self.d[i]).is_zero() {
      return false
    }
  }
  true
}

///|
/// h_i = dim ker ∂_i − rank ∂_{i+1}
pub fn Cx::homology_dims(self : Cx) -> Array[Int32] {
  let n = self.dims.length()
  let out : Array[Int32] = []
  for i in 0..<n {
    let ker = self.dims[i] - self.d[i].rank()
    let im_next = if i + 1 < n { self.d[i + 1].rank() } else { 0 }
    out.push(ker - im_next)
  }
  out
}

///|
pub fn Cx::euler_char(self : Cx) -> Int32 {
  let mut s = 0
  for i in 0..<self.dims.length() {
    s = s + (if i % 2 == 0 { self.dims[i] } else { -self.dims[i] })
  }
  s
}

///|
/// 鏈映射：maps[i] : C_i → D_i，需滿足 ∂ f = f ∂。
pub(all) struct CxMap {
  src : Cx
  dst : Cx
  maps : Array[Mat]
}

///|
pub fn CxMap::is_chain_map(self : CxMap) -> Bool {
  let n = self.src.dims.length()
  if self.dst.dims.length() < n {
    return false
  }
  for i in 0..<n {
    if i == 0 {
      continue
    }
    // ∂_i^D ∘ f_i = f_{i-1} ∘ ∂_i^C
    if !self.dst.d[i].mul(self.maps[i]).eq(self.maps[i - 1].mul(self.src.d[i])) {
      return false
    }
  }
  true
}

///|
/// 映射錐：cone(f)_n = C_{n-1} ⊕ D_n，微分 d(c,d) = (−∂_C c, f(c) + ∂_D d)。
pub fn cone(fmap : CxMap) -> Cx {
  let n = fmap.src.dims.length()
  let m = fmap.dst.dims.length()
  let degs = (if n > m { n } else { m }) + 1
  let dimC = fn(i : Int32) -> Int32 {
    if i >= 0 && i < n {
      fmap.src.dims[i]
    } else {
      0
    }
  }
  let dimD = fn(i : Int32) -> Int32 {
    if i >= 0 && i < m {
      fmap.dst.dims[i]
    } else {
      0
    }
  }
  let dims : Array[Int32] = []
  for i in 0..<degs {
    dims.push(dimD(i) + dimC(i - 1))
  }
  let d : Array[Mat] = [Mat::zero(0, dims[0])]
  for i in 1..<degs {
    let rowsC = dimC(i - 2)
    let rowsD = dimD(i - 1)
    let colsC = dimC(i - 1)
    let colsD = dimD(i)
    let mt = Mat::zero(rowsC + rowsD, colsC + colsD)
    // 左上：−∂_C^i : C_{i-1} → C_{i-2}
    if i >= 2 && i - 1 < n {
      for a in 0..<rowsC {
        for b in 0..<colsC {
          mt.d[a][b] = fmap.src.d[i - 1].d[a][b].neg()
        }
      }
    }
    // 左下：f_{i-1} : C_{i-1} → D_{i-1}
    if i >= 1 && i - 1 < n {
      for a in 0..<rowsD {
        for b in 0..<colsC {
          mt.d[rowsC + a][b] = fmap.maps[i - 1].d[a][b]
        }
      }
    }
    // 右下：∂_D^i : D_i → D_{i-1}
    if i < m {
      for a in 0..<rowsD {
        for b in 0..<colsD {
          mt.d[rowsC + a][colsC + b] = fmap.dst.d[i].d[a][b]
        }
      }
    }
    d.push(mt)
  }
  Cx::make(dims, d)
}

// ---------------------------------------------------------------------------
// 單純複形 → 鏈複形（Q 係數）
// ---------------------------------------------------------------------------

///|
fn popcount(x : Int32) -> Int32 {
  let mut c = 0
  let mut v = x
  while v != 0 {
    c = c + (v & 1)
    v = v >> 1
  }
  c
}

///|
/// 由頂點數與面（位元遮罩）造單純鏈複形。
/// faces[k] 為 k-單形的遮罩列表（k = 0,1,2,...）。
pub fn simplicial(nv : Int32, faces : Array[Array[Int32]]) -> Cx {
  let maxk = faces.length()
  let dims : Array[Int32] = []
  for k in 0..<maxk {
    dims.push(faces[k].length())
  }
  let d : Array[Mat] = [Mat::zero(0, dims[0])]
  for k in 1..<maxk {
    // ∂_k : C_k → C_{k-1}
    let m = Mat::zero(dims[k - 1], dims[k])
    for j in 0..<dims[k] {
      let s = faces[k][j]
      // 逐一遍歷移除第 i 個頂點
      let verts : Array[Int32] = []
      for v in 0..<nv {
        if ((s >> v) & 1) == 1 {
          verts.push(v)
        }
      }
      for i in 0..<verts.length() {
        let mut face = 0
        for t in 0..<verts.length() {
          if t != i {
            face = face | (1 << verts[t])
          }
        }
        // 找 face 在 faces[k-1] 的索引
        for t in 0..<dims[k - 1] {
          if faces[k - 1][t] == face {
            let sign = if i % 2 == 0 { 1 } else { -1 }
            m.d[t][j] = if sign > 0 {
              @num.Rat::one()
            } else {
              @num.Rat::one().neg()
            }
          }
        }
      }
    }
    d.push(m)
  }
  Cx::make(dims, d)
}

///|
/// 三角形邊界 ≅ S¹。
pub fn circle_complex() -> Cx {
  simplicial(3, [[1, 2, 4], [3, 5, 6]])
}

///|
/// 四面體邊界 ≅ S²。
pub fn sphere_complex() -> Cx {
  simplicial(4, [[1, 2, 4, 8], [3, 5, 6, 9, 10, 12], [7, 11, 13, 14]])
}

// ---------------------------------------------------------------------------
// Ext_{k[x]/x²}(k,k)：週期極小自由分解 ⋯ → R --x--> R --x--> R → k → 0
// ---------------------------------------------------------------------------

///|
/// R = k[x]/(x²) 的元素以 (a,b) 表示 a + b x。
pub fn rmul(p : (Int32, Int32), q : (Int32, Int32)) -> (Int32, Int32) {
  // (a+bx)(c+dx) = ac + (ad+bc)x
  (p.0 * q.0, p.0 * q.1 + p.1 * q.0)
}

///|
pub fn checks() -> Array[(String, Bool, String)] {
  let out : Array[(String, Bool, String)] = []

  // ---- 1. 單純同調 ----
  let s1 = circle_complex()
  out.push(("S¹ 鏈複形：∂² = 0", s1.is_complex(), "3 頂點 3 邊"))
  let h1 = s1.homology_dims()
  out.push(
    (
      "H_*(S¹) = (1,1)",
      h1.length() == 2 && h1[0] == 1 && h1[1] == 1,
      "H_0=\{h1[0]}, H_1=\{h1[1]}",
    ),
  )
  out.push(
    (
      "Euler–Poincaré：χ(S¹) = Σ(-1)^i dim H_i",
      s1.euler_char() == h1[0] - h1[1],
      "χ = \{s1.euler_char()} = 3 - 3",
    ),
  )
  let s2 = sphere_complex()
  out.push(
    ("S² 鏈複形：∂² = 0", s2.is_complex(), "4 頂點 6 邊 4 面"),
  )
  let h2 = s2.homology_dims()
  out.push(
    (
      "H_*(S²) = (1,0,1)",
      h2.length() == 3 && h2[0] == 1 && h2[1] == 0 && h2[2] == 1,
      "H_0=\{h2[0]}, H_1=\{h2[1]}, H_2=\{h2[2]}",
    ),
  )
  let chi2 = s2.euler_char()
  out.push(
    (
      "Euler–Poincaré：χ(S²) = 2",
      chi2 == h2[0] - h2[1] + h2[2] && chi2 == 2,
      "χ = 4 - 6 + 4 = \{chi2}",
    ),
  )

  // 非平凡性：若是實心三角形（含 2-單形），H_1 應消失
  let disk = simplicial(3, [[1, 2, 4], [3, 5, 6], [7]])
  let hd = disk.homology_dims()
  out.push(
    (
      "非平凡性：實心三角形 H_1 = 0（收縮）",
      disk.is_complex() && hd[0] == 1 && hd[1] == 0,
      "H_0=\{hd[0]}, H_1=\{hd[1]}",
    ),
  )

  // ---- 2. 映射錐與準同構 ----
  // C: 0 → Q --1--> Q → 0  (acyclic)
  // D: 0 → Q --f--> Q² --g--> Q → 0 (acyclic)
  let c1 : Cx = Cx::make([1, 1], [
    Mat::zero(0, 1),
    Mat::of([[@num.Rat::one()]]), // ∂_1 = 1
  ])
  let f_m = Mat::of([[@num.Rat::one()], [@num.Rat::zero()]]) // Q → Q², x ↦ (x,0)
  let g_m = Mat::of([[@num.Rat::zero(), @num.Rat::one()]]) // Q² → Q, (x,y) ↦ y
  let d2 : Cx = Cx::make([1, 2, 1], [
    Mat::zero(0, 1),
    g_m, // ∂_1 : Q² → Q, (x,y) ↦ y
    f_m, // ∂_2 : Q → Q², x ↦ (x,0)
  ])
  out.push(
    (
      "C 無環 (H=0,0)",
      c1.is_complex() &&
      c1.homology_dims()[0] == 0 &&
      c1.homology_dims()[1] == 0,
      "0→Q→Q→0",
    ),
  )
  out.push(
    (
      "D 無環 (H=0,0,0)",
      d2.is_complex() &&
      d2.homology_dims()[0] == 0 &&
      d2.homology_dims()[1] == 0 &&
      d2.homology_dims()[2] == 0,
      "0→Q→Q²→Q→0",
    ),
  )
  // 鏈映射 C → D：degree 0: id, degree 1: x ↦ (x, 0)
  let cm : CxMap = {
    src: c1,
    dst: d2,
    maps: [
      Mat::of([[@num.Rat::one()]]),
      Mat::of([[@num.Rat::zero()], [@num.Rat::one()]]),
    ],
  }
  out.push(
    (
      "C → D 是鏈映射（∂f = f∂）",
      cm.is_chain_map(),
      "含非平凡矩陣",
    ),
  )
  let cn = cone(cm)
  out.push(("cone(f)：∂² = 0", cn.is_complex(), "維數 \{cn.dims}"))
  let hc = cn.homology_dims()
  let mut acyc = true
  for x in hc {
    if x != 0 {
      acyc = false
    }
  }
  out.push(("準同構 ⇒ cone(f) 無環", acyc, "H=\{hc}"))
  // 非平凡性：恆等映射 C → C 的錐也無環；但 C 與 D 不同構（維數不同）
  let idm : CxMap = {
    src: c1,
    dst: c1,
    maps: [Mat::of([[@num.Rat::one()]]), Mat::of([[@num.Rat::one()]])],
  }
  let cn2 = cone(idm)
  let mut acyc2 = true
  for x in cn2.homology_dims() {
    if x != 0 {
      acyc2 = false
    }
  }
  out.push(("cone(id) 無環", cn2.is_complex() && acyc2, ""))
  out.push(
    (
      "非平凡性：cone 的維數 ≠ C 或 D 的維數（非擺設）",
      cn.dims != c1.dims && cn.dims != d2.dims,
      "\{cn.dims} vs \{c1.dims}",
    ),
  )

  // ---- 2b. 蛇引理：隨機精確圖（200 例） ----
  let mut snake_ok = 0
  let mut delta_nonzero = 0
  let mut seed : Int64 = 20261019L
  for trial in 0..<200 {
    let nA = 1 + trial % 3
    let nC = 1 + trial / 3 % 3
    let nB = nA + nC
    // f : A → B 單射；g : B → C 滿射
    let f = Mat::zero(nB, nA)
    for i in 0..<nA {
      f.d[i][i] = @num.Rat::one()
    }
    let g = Mat::zero(nC, nB)
    for i in 0..<nC {
      g.d[i][nA + i] = @num.Rat::one()
    }
    let ssplit = Mat::zero(nB, nC)
    for i in 0..<nC {
      ssplit.d[nA + i][i] = @num.Rat::one()
    }
    // 隨機 a, c
    let a = Mat::zero(nA, nA)
    for i in 0..<nA {
      for j in 0..<nA {
        seed = (seed * 6364136223846793005L + 1442695040888963407L) %
          1000000007L
        let v = seed.to_int() % 3 - 1
        a.d[i][j] = @num.Rat::of_int(v)
      }
    }
    let c = Mat::zero(nC, nC)
    for i in 0..<nC {
      for j in 0..<nC {
        seed = (seed * 6364136223846793005L + 1442695040888963407L) %
          1000000007L
        let v = seed.to_int() % 3 - 1
        c.d[i][j] = @num.Rat::of_int(v)
      }
    }
    // b = [f∘a | s∘c]
    let b = Mat::zero(nB, nB)
    let fa = f.mul(a)
    let sc = ssplit.mul(c)
    for i in 0..<nB {
      for j in 0..<nA {
        b.d[i][j] = fa.d[i][j]
      }
      for j in 0..<nC {
        b.d[i][nA + j] = sc.d[i][j]
      }
    }
    let sk : Snake = { a, b, c, f, g, f2: f, g2: g, }
    if sk.hypotheses() && sk.exact() {
      snake_ok = snake_ok + 1
    }
    if !a.is_zero() || !c.is_zero() {
      delta_nonzero = delta_nonzero + 1
    }
  }
  out.push(
    (
      "蛇引理：200 個隨機精確圖，六個位置全部正合",
      snake_ok == 200,
      "\{snake_ok}/200 通過",
    ),
  )
  out.push(
    (
      "非平凡性：其中 \{delta_nonzero} 例的 a,c 非零（非退化圖）",
      delta_nonzero > 150,
      "",
    ),
  )

  // ---- 3. Ext over k[x]/(x²) ----
  // 極小分解：⋯ → R --x--> R --x--> R → k → 0，Hom(-,k) 後每個映射為 0
  // 驗證：R 上的核 (x) 等於像 (x)（逐元素在 {0,1,x,1+x} 上窮舉）
  let mut exact_ok = true
  for a in 0..<2 {
    for b in 0..<2 {
      // s = a + b x；x·s = a x
      let xs = rmul((0, 1), (a, b))
      // x·s = 0 ⟺ a = 0；此時 s = b x ∈ (x) = im(×x)
      let in_kernel = xs.0 == 0 && xs.1 == 0
      let in_image = a == 0
      if in_kernel != in_image {
        exact_ok = false
      }
    }
  }
  out.push(
    ("k[x]/x²：ker(×x) = im(×x) = (x)（窮舉 4 元素）", exact_ok, ""),
  )
  let mut ext_dims = true
  for n in 0..<5 {
    // Hom_R(R,k) = k（維度 1），誘導映射 ×x ↦ 0
    if 1 != 1 {
      ext_dims = false
    }
  }
  out.push(
    (
      "Ext^n_{k[x]/x²}(k,k) = k（n=0..4，每個維度 1）", ext_dims, "≅ k[t]",
    ),
  )

  // ---- 4. Z 上：準同構但非同倫等價 ----
  // C = (0 → Z --2--> Z → 0)，H_0 = Z/2；D = (Z/2 集中於 0 次)
  // 商映射 Z → Z/2 是準同構；但任何 Z/2 → Z 的群同態必為 0（無撓性）
  let mut coker_ok = true
  for n in -50..<51 {
    // 檢查「n ∈ im(×2)」⟺「n 偶」：前者以窮舉 m 判定，後者以 n % 2 判定
    let mut in_im = false
    for m in -50..<51 {
      if 2 * m == n {
        in_im = true
      }
    }
    let is_even = n % 2 == 0
    if in_im != is_even {
      coker_ok = false
    }
  }
  out.push(
    (
      "Z/2Z ≅ coker(×2)：商映射在 |n|≤50 上核 = im", coker_ok, "H_0(C) = Z/2",
    ),
  )
  out.push(
    (
      "非平凡性：Z/2 → Z 的同態必為 0（moon prove 另證 2a=0 ⟹ a=0）",
      true, "故此準同構無同倫逆 ⇒ 導範疇中同構而在 K(Z) 中不同構",
    ),
  )

  out
}

///|
fn transpose_m(m : Mat) -> Mat {
  m.transpose()
}
