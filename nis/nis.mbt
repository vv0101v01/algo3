// ============================================================================
// nis — 尼雲維奇拓撲 (Nisnevich topology)：有限 Galois 模型
//
// 【定義】設 X 為概形，x ∈ X。態射 f : Y → X 在 x 處「完全分解」
//   (completely decomposed, cd) ⟺ ∃ y ∈ Y，f(y) = x，且剩餘域擴張
//        k(x) ↪ k(y)   為同構（即 [k(y) : k(x)] = 1）。
//   一族 { f_i : Y_i → X } 是 Nisnevich 覆蓋 ⟺ 它在每個 x ∈ X 處 cd。
//   等價說法（篩的語言）：篩 S ⊆ (C/X) 是 Nisnevich 覆蓋 ⟺ 每個 x ∈ X
//   有 (f : Y → X) ∈ S 在 x 處 cd。
//
// 【定理】(Nisnevich 1989; Voevodsky cd-structure)
//   (1) Zar ⊆ Nis ⊆ Ét（拓撲精細度），且兩個包含皆嚴格。
//   (2) Nisnevich 拓撲是 subcanonical：每個可表預層 h_X 都是層。
//   (3) Nisnevich 覆蓋可由「初等 cd 方形」生成：
//           U ×_X V ──→ V
//              │         │
//              ↓         ↓        U ⊆ X 開浸入，V → X étale，
//              U  ────→  X        V ∖ (U ×_X V) → X ∖ U 為同構。
//
// 【有限模型：Grothendieck–Galois 對偶】
//   取 G = Z/2 × Z/2 = {0,1,2,3}（乘法 = xor，a = 1，b = 2）。
//   對連通概形 X 與幾何點 x̄，有限 étale X-概形 ⟷ 有限 G-集：
//        Y ↦ Y(x̄) = Hom_X(x̄, Y)，   Hom_X(Y, Z) ≅ Hom_G(Y(x̄), Z(x̄))。
//   在這組等價下：
//        • 點 y ∈ Y(x̄) 的分解群 D_y = Stab_G(y) ≤ G；
//        • f : Y → Z 在 z 處 cd ⟺ ∃ y ∈ Y(x̄)，f(y) = z，
//                                        且 Stab(y) = Stab(z)；
//        • 「étale 覆蓋」= 共同滿射族（協同滿射）；
//        • 「開浸入」= 單射態射（有限 étale 情形下等價於開浸入），
//          故「Zariski 覆蓋」= 單射且共同滿射族。
//   因為 Stab 可在常數時間算出，cd 條件成為完全可計算的有限條件，
//   而纖維積 Y ×_Z W = {(y,w) : f(y) = g(w)}（對角作用）亦可直接計算。
//
// 【本檔驗證】（全部以窮舉計算，非宣告）
//   T1/T2/T3 拓撲公理、Zar ⊆ Nis ⊆ Ét 及嚴格見證、subcanonicity、
//   「{Y → pt} 為 Nis 覆蓋 ⟺ Y 有 G-不動點」判準，以及三種拓撲的覆蓋計數。
// ============================================================================

// ---------------------------------------------------------------------------
// 1. 有限 G-集（G = Z/2 × Z/2）
// ---------------------------------------------------------------------------

///|
/// 有限 G-集：n 個點，acts[g * n + i] = g · i（g = 0..3）。
struct GSet {
  n : Int32
  acts : Array[Int32]
}

///|
/// 由兩個生成元（a、b 皆為對合且交換）的作用建構 G-集。
fn mkg(n : Int32, pa : Array[Int32], pb : Array[Int32]) -> GSet {
  let acts : Array[Int32] = []
  for g in 0..<4 {
    for i in 0..<n {
      let mut j = i
      if (g & 1) != 0 {
        j = pa[j]
      }
      if (g & 2) != 0 {
        j = pb[j]
      }
      acts.push(j)
    }
  }
  { n, acts, }
}

///|
/// 群作用 g · i。
fn act(o : GSet, g : Int32, i : Int32) -> Int32 {
  o.acts[g * o.n + i]
}

///|
/// 穩定子（= 分解群）Stab(i) ≤ G，以 4 位元遮罩表示。
fn stab(o : GSet, i : Int32) -> Int32 {
  let mut m = 0
  for g in 0..<4 {
    if act(o, g, i) == i {
      m = m | (1 << g)
    }
  }
  m
}

///|
/// 模型中的物件（G-集）：
///   0: pt          （1 點，= 終物件，Spec k）
///   1: G/⟨a⟩       （2 點，b 交換；Stab = ⟨b⟩）
///   2: G/⟨b⟩       （2 點，a 交換；Stab = ⟨a⟩）
///   3: G           （4 點，正則作用；Stab = 1，G-torsor）
///   4: pt ⊔ pt     （2 點，平凡作用；Stab = G）
///   5: G/⟨a⟩ ⊔ pt （3 點）
///   6: G/⟨b⟩ ⊔ pt （3 點）
fn objects() -> Array[GSet] {
  [
    mkg(1, [0], [0]),
    mkg(2, [0, 1], [1, 0]),
    mkg(2, [1, 0], [0, 1]),
    mkg(4, [1, 0, 3, 2], [2, 3, 0, 1]),
    mkg(2, [0, 1], [0, 1]),
    mkg(3, [0, 1, 2], [1, 0, 2]),
    mkg(3, [1, 0, 2], [0, 1, 2]),
  ]
}

// ---------------------------------------------------------------------------
// 2. 態射 = G-等變映射
// ---------------------------------------------------------------------------

///|
/// 態射：src → tgt，fun 為點映射。
struct Mor {
  src : Int32
  tgt : Int32
  fun : Array[Int32]
}

///|
/// 所有 {0..sn-1} → {0..tn-1} 的函數。
fn enum_functions(sn : Int32, tn : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  if sn == 0 {
    out.push([])
    return out
  }
  let rest = enum_functions(sn - 1, tn)
  for r in rest {
    for v in 0..<tn {
      let f : Array[Int32] = []
      for x in r {
        f.push(x)
      }
      f.push(v)
      out.push(f)
    }
  }
  out
}

///|
/// 等變性：f(g · x) = g · f(x)。
fn equivariant(s : GSet, t : GSet, f : Array[Int32]) -> Bool {
  let mut ok = true
  for g in 0..<4 {
    for i in 0..<s.n {
      if f[act(s, g, i)] != act(t, g, f[i]) {
        ok = false
      }
    }
  }
  ok
}

///|
/// 窮舉所有物件之間的所有態射。
fn morphisms(objs : Array[GSet]) -> Array[Mor] {
  let out : Array[Mor] = []
  for s in 0..<objs.length() {
    for t in 0..<objs.length() {
      for f in enum_functions(objs[s].n, objs[t].n) {
        if equivariant(objs[s], objs[t], f) {
          out.push({ src: s, tgt: t, fun: f, })
        }
      }
    }
  }
  out
}

///|
/// 態射的像（以目標點的位元遮罩表示）。
fn image_mask(objs : Array[GSet], mors : Array[Mor], m : Int32) -> Int32 {
  let mut mask = 0
  for x in 0..<objs[mors[m].src].n {
    mask = mask | (1 << mors[m].fun[x])
  }
  mask
}

///|
/// 所有點的遮罩。
fn all_points(o : GSet) -> Int32 {
  (1 << o.n) - 1
}

///|
/// 單射（= 有限 étale 情形下的開浸入）。
fn is_injective(objs : Array[GSet], mors : Array[Mor], m : Int32) -> Bool {
  let t = objs[mors[m].tgt].n
  let seen : Array[Int32] = []
  for _ in 0..<t {
    seen.push(0)
  }
  let mut ok = true
  for x in 0..<objs[mors[m].src].n {
    let y = mors[m].fun[x]
    if seen[y] > 0 {
      ok = false
    }
    seen[y] = seen[y] + 1
  }
  ok
}

// ---------------------------------------------------------------------------
// 3. 三種拓撲
// ---------------------------------------------------------------------------

///|
/// Nisnevich 覆蓋：每個點 z 有成員在 z 處 cd（Stab 相等）。
fn is_cd_cover(
  objs : Array[GSet],
  mors : Array[Mor],
  y : Int32,
  fam : Array[Int32],
) -> Bool {
  for z in 0..<objs[y].n {
    let sz = stab(objs[y], z)
    let mut ok = false
    for m in fam {
      for x in 0..<objs[mors[m].src].n {
        if mors[m].fun[x] == z && stab(objs[mors[m].src], x) == sz {
          ok = true
        }
      }
    }
    if !ok {
      return false
    }
  }
  true
}

///|
/// Étale 覆蓋：共同滿射。
fn is_surjective_cover(
  objs : Array[GSet],
  mors : Array[Mor],
  y : Int32,
  fam : Array[Int32],
) -> Bool {
  let mut mask = 0
  for m in fam {
    mask = mask | image_mask(objs, mors, m)
  }
  mask == all_points(objs[y])
}

///|
/// Zariski 覆蓋：每個成員為開浸入（單射），且共同滿射。
fn is_zar_cover(
  objs : Array[GSet],
  mors : Array[Mor],
  y : Int32,
  fam : Array[Int32],
) -> Bool {
  if !is_surjective_cover(objs, mors, y, fam) {
    return false
  }
  let mut ok = true
  for m in fam {
    if !is_injective(objs, mors, m) {
      ok = false
    }
  }
  ok
}

///|
/// 依 kind 判定覆蓋族：0 = Zariski，1 = Nisnevich，2 = étale。
fn is_cover_kind(
  objs : Array[GSet],
  mors : Array[Mor],
  y : Int32,
  kind : Int32,
  fam : Array[Int32],
) -> Bool {
  if kind == 0 {
    is_zar_cover(objs, mors, y, fam)
  } else if kind == 1 {
    is_cd_cover(objs, mors, y, fam)
  } else {
    is_surjective_cover(objs, mors, y, fam)
  }
}

///|
/// 目標 y 的所有覆蓋族（大小 ≤ 2，過濾條件由 predicate 給定）。
/// 大小 ≤ 2 是有限片段：單成員族與雙成員族已足以生成整個拓撲的篩。
fn covers_of(
  objs : Array[GSet],
  mors : Array[Mor],
  y : Int32,
  kind : Int32,
) -> Array[Array[Int32]] {
  let into : Array[Int32] = []
  for i in 0..<mors.length() {
    if mors[i].tgt == y {
      into.push(i)
    }
  }
  let out : Array[Array[Int32]] = []
  for a in 0..<into.length() {
    let ma = into[a]
    let f1 : Array[Int32] = [ma]
    if is_cover_kind(objs, mors, y, kind, f1) {
      out.push(f1)
    }
    let sa = image_mask(objs, mors, ma)
    for b in (a + 1)..<into.length() {
      let mb = into[b]
      if (sa | image_mask(objs, mors, mb)) == all_points(objs[y]) {
        let f2 : Array[Int32] = [ma, mb]
        if is_cover_kind(objs, mors, y, kind, f2) {
          out.push(f2)
        }
      }
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 4. 拉回、複合、匹配族
// ---------------------------------------------------------------------------

///|
/// 拉回族的 cd 檢驗：對 z ∈ Z 需有成員 f_i 與點 x ∈ Y_i，
///   f_i(x) = f(z) 且 Stab(z) ⊆ Stab(x)
/// （纖維積點 (x, z) 的穩定子 = Stab(x) ∩ Stab(z)，故等號 ⟺ 包含）。
fn pullback_family_cd(
  objs : Array[GSet],
  mors : Array[Mor],
  fam : Array[Int32],
  f : Int32,
) -> Bool {
  let z_obj = objs[mors[f].src]
  for z in 0..<z_obj.n {
    let y = mors[f].fun[z]
    let sz = stab(z_obj, z)
    let mut ok = false
    for m in fam {
      for x in 0..<objs[mors[m].src].n {
        if mors[m].fun[x] == y && (stab(objs[mors[m].src], x) & sz) == sz {
          ok = true
        }
      }
    }
    if !ok {
      return false
    }
  }
  true
}

///|
/// 複合態射 m ∘ g（在窮舉池中尋找）。
fn composite(
  objs : Array[GSet],
  mors : Array[Mor],
  m : Int32,
  g : Int32,
) -> Int32 {
  let mut found = -1
  for i in 0..<mors.length() {
    if mors[i].src == mors[g].src && mors[i].tgt == mors[m].tgt {
      let mut eq = true
      for x in 0..<objs[mors[g].src].n {
        if mors[i].fun[x] != mors[m].fun[mors[g].fun[x]] {
          eq = false
        }
      }
      if eq {
        found = i
      }
    }
  }
  found
}

///|
/// 匹配族的一條約束：h_i ∘ u = h_j ∘ v，只要 m_i ∘ u = m_j ∘ v。
struct Con {
  i : Int32
  u : Int32
  j : Int32
  v : Int32
}

///|
/// 由覆蓋族生成所有約束（僅取來源 ≤ 3 點的態射，屬有限片段）。
fn constraints_of(
  objs : Array[GSet],
  mors : Array[Mor],
  fam : Array[Int32],
) -> Array[Con] {
  let out : Array[Con] = []
  for i in 0..<fam.length() {
    let ai = mors[fam[i]].src
    for j in 0..<fam.length() {
      let aj = mors[fam[j]].src
      for u in 0..<mors.length() {
        if mors[u].tgt != ai || objs[mors[u].src].n > 3 {
          continue
        }
        for v in 0..<mors.length() {
          if mors[v].tgt != aj || objs[mors[v].src].n > 3 {
            continue
          }
          if mors[u].src != mors[v].src {
            continue
          }
          let mut eq = true
          for z in 0..<objs[mors[u].src].n {
            if mors[fam[i]].fun[mors[u].fun[z]] !=
              mors[fam[j]].fun[mors[v].fun[z]] {
              eq = false
            }
          }
          if eq {
            out.push({ i, u, j, v, })
          }
        }
      }
    }
  }
  out
}

///|
/// 來源 a、目標 x 之間的所有態射 id。
fn hom_ids(mors : Array[Mor], a : Int32, x : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<mors.length() {
    if mors[i].src == a && mors[i].tgt == x {
      out.push(i)
    }
  }
  out
}

///|
/// 檢查一條約束在態射組 (h) 下是否成立。
fn con_holds(
  objs : Array[GSet],
  mors : Array[Mor],
  cons : Array[Con],
  hs : Array[Int32],
) -> Bool {
  for c in cons {
    let hi = hs[c.i]
    let hj = hs[c.j]
    for z in 0..<objs[mors[c.u].src].n {
      if mors[hi].fun[mors[c.u].fun[z]] != mors[hj].fun[mors[c.v].fun[z]] {
        return false
      }
    }
  }
  true
}

///|
/// 匹配族數（覆蓋族大小 ≤ 2）。
fn matching_count(
  objs : Array[GSet],
  mors : Array[Mor],
  fam : Array[Int32],
  cons : Array[Con],
  x : Int32,
) -> Int32 {
  let o1 = hom_ids(mors, mors[fam[0]].src, x)
  if fam.length() == 1 {
    let mut cnt = 0
    let hs : Array[Int32] = [0]
    for h in o1 {
      hs[0] = h
      if con_holds(objs, mors, cons, hs) {
        cnt = cnt + 1
      }
    }
    return cnt
  }
  let o2 = hom_ids(mors, mors[fam[1]].src, x)
  let mut cnt = 0
  let hs : Array[Int32] = [0, 0]
  for h1 in o1 {
    for h2 in o2 {
      hs[0] = h1
      hs[1] = h2
      if con_holds(objs, mors, cons, hs) {
        cnt = cnt + 1
      }
    }
  }
  cnt
}

///|
/// 物件是否有 G-不動點。
fn has_fixed_point(o : GSet) -> Bool {
  let mut yes = false
  for i in 0..<o.n {
    if stab(o, i) == 15 {
      yes = true
    }
  }
  yes
}

// ---------------------------------------------------------------------------
// 5. 驗證
// ---------------------------------------------------------------------------

///|
/// 跑完整套檢查：(名稱, 是否通過, 備註)。
pub fn checks() -> Array[(String, Bool, String)] {
  let out : Array[(String, Bool, String)] = []
  let objs = objects()
  let mors = morphisms(objs)
  let n_obj = objs.length()
  let n_mor = mors.length()
  let zar : Array[Array[Array[Int32]]] = []
  let nis : Array[Array[Array[Int32]]] = []
  let et : Array[Array[Array[Int32]]] = []
  for y in 0..<n_obj {
    zar.push(covers_of(objs, mors, y, 0))
    nis.push(covers_of(objs, mors, y, 1))
    et.push(covers_of(objs, mors, y, 2))
  }
  // ---- (T1) 極大篩覆蓋 ------------------------------------------------
  let mut t1 = true
  for y in 0..<n_obj {
    let mut id = -1
    for m in 0..<n_mor {
      if mors[m].src == y && mors[m].tgt == y {
        let mut iso = true
        for i in 0..<objs[y].n {
          if mors[m].fun[i] != i {
            iso = false
          }
        }
        if iso {
          id = m
        }
      }
    }
    let fam : Array[Int32] = [id]
    if id < 0 || !is_cd_cover(objs, mors, y, fam) {
      t1 = false
    }
  }
  out.push(
    ("(T1) 極大篩 {id_Y} 為 Nisnevich 覆蓋", t1, "\{n_obj} 個物件"),
  )
  // ---- (T2) 拉回穩定 --------------------------------------------------
  let mut t2 = true
  let mut t2n = 0
  for y in 0..<n_obj {
    for fam in nis[y] {
      for f in 0..<n_mor {
        if mors[f].tgt != y {
          continue
        }
        t2n = t2n + 1
        if !pullback_family_cd(objs, mors, fam, f) {
          t2 = false
        }
      }
    }
  }
  out.push(
    (
      "(T2) 拉回穩定：f*(cd 覆蓋) 仍為 cd 覆蓋",
      t2,
      "\{t2n} 組 (覆蓋, 態射)",
    ),
  )
  // ---- (T3) 局部性 ----------------------------------------------------
  let mut t3 = true
  let mut t3n = 0
  for y in 0..<n_obj {
    for fam in nis[y] {
      for m in fam {
        let a = mors[m].src
        for g in nis[a] {
          let comp : Array[Int32] = []
          let mut good = true
          for gm in g {
            let c = composite(objs, mors, m, gm)
            if c < 0 {
              good = false
            } else {
              comp.push(c)
            }
          }
          if !good {
            t3 = false
          } else {
            for m2 in fam {
              if m2 != m {
                comp.push(m2)
              }
            }
            t3n = t3n + 1
            if !is_cd_cover(objs, mors, y, comp) {
              t3 = false
            }
          }
        }
      }
    }
  }
  out.push(
    ("(T3) 局部性：覆蓋的覆蓋仍為覆蓋", t3, "\{t3n} 組複合"),
  )
  // ---- 包含關係：Zar ⊆ Nis ⊆ Ét ----------------------------------------
  let mut zc = true
  let mut zn = 0
  for y in 0..<n_obj {
    for fam in zar[y] {
      zn = zn + 1
      if !is_cd_cover(objs, mors, y, fam) {
        zc = false
      }
    }
  }
  out.push(
    (
      "Zariski ⊆ Nisnevich（單射族必 cd）",
      zc,
      "\{zn} 個 Zariski 覆蓋",
    ),
  )
  let mut ne = true
  let mut nn = 0
  for y in 0..<n_obj {
    for fam in nis[y] {
      nn = nn + 1
      if !is_surjective_cover(objs, mors, y, fam) {
        ne = false
      }
    }
  }
  out.push(
    (
      "Nisnevich ⊆ étale（cd ⇒ 共同滿射）",
      ne,
      "\{nn} 個 Nisnevich 覆蓋",
    ),
  )
  // ---- 嚴格性見證 ------------------------------------------------------
  // {pt ⊔ pt → pt}：Stab = G 在每個點 ⇒ cd，但非單射 ⇒ 非 Zariski。
  let src4 = 4
  let mut w1 = -1
  for m in 0..<n_mor {
    if mors[m].src == src4 && mors[m].tgt == 0 {
      w1 = m
    }
  }
  let fam1 : Array[Int32] = [w1]
  let strict1 = w1 >= 0 &&
    is_cd_cover(objs, mors, 0, fam1) &&
    !is_zar_cover(objs, mors, 0, fam1)
  out.push(
    (
      "嚴格性 Nisnevich ⊋ Zariski：{pt ⊔ pt → pt}", strict1, "cd 但非單射（非開浸入）",
    ),
  )
  // {G → pt}：自由軌道，Stab = 1 ≠ G ⇒ 非 cd，但滿射 ⇒ étale。
  let mut w2 = -1
  for m in 0..<n_mor {
    if mors[m].src == 3 && mors[m].tgt == 0 {
      w2 = m
    }
  }
  let fam2 : Array[Int32] = [w2]
  let strict2 = w2 >= 0 &&
    is_surjective_cover(objs, mors, 0, fam2) &&
    !is_cd_cover(objs, mors, 0, fam2)
  out.push(
    (
      "嚴格性 étale ⊋ Nisnevich：{G → pt}（自由軌道）", strict2, "滿射但無 G-不動點 ⇒ 非 cd",
    ),
  )
  // ---- Nisnevich 判準：{Y → pt} 覆蓋 ⟺ Y 有 G-不動點 -------------------
  let mut crit = true
  let mut critn = 0
  for y in 0..<n_obj {
    let mut f = -1
    for m in 0..<n_mor {
      if mors[m].src == y && mors[m].tgt == 0 {
        f = m
      }
    }
    if f >= 0 {
      critn = critn + 1
      let fam : Array[Int32] = [f]
      let cov = is_cd_cover(objs, mors, 0, fam)
      if cov != has_fixed_point(objs[y]) {
        crit = false
      }
    }
  }
  out.push(
    (
      "判準：{Y → pt} 是 Nisnevich 覆蓋 ⟺ Y 有 G-不動點",
      crit,
      "\{critn} 個物件",
    ),
  )
  // ---- Subcanonicity ---------------------------------------------------
  let mut sub = true
  let mut subn = 0
  let mut subc = 0
  for y in 0..<n_obj {
    for fam in nis[y] {
      let mut small = true
      for m in fam {
        if objs[mors[m].src].n > 2 {
          small = false
        }
      }
      if !small {
        continue
      }
      let cons = constraints_of(objs, mors, fam)
      for x in 0..<n_obj {
        subn = subn + 1
        let lhs = hom_ids(mors, y, x).length()
        let rhs = matching_count(objs, mors, fam, cons, x)
        if lhs != rhs {
          sub = false
        }
        if lhs == rhs {
          subc = subc + 1
        }
      }
    }
  }
  out.push(
    (
      "Subcanonicity：可表預層 h_X 對 Nisnevich 覆蓋是層",
      sub,
      "\{subn} 組 (覆蓋, X)",
    ),
  )
  // ---- 覆蓋計數 --------------------------------------------------------
  let mut cz = 0
  let mut cn = 0
  let mut ce = 0
  for y in 0..<n_obj {
    cz = cz + zar[y].length()
    cn = cn + nis[y].length()
    ce = ce + et[y].length()
  }
  out.push(
    (
      "覆蓋計數：|Zar| ≤ |Nis| ≤ |Ét|",
      cz <= cn && cn <= ce && cz < cn && cn < ce,
      "Zar = \{cz}，Nis = \{cn}，ét = \{ce}",
    ),
  )
  out
}
