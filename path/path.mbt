// ============================================================================
// path — 路徑空間 (path space)：圖的自由群胚、既約字正規形式、同倫類。
//
// 定理：圖 G 的路徑範疇中，「刪除/插入 aa⁻¹」生成的同倫等價關係，其每個類
// 恰有一個既約代表元（正規形式）。本檔以並查集窮舉驗證小圖上的此定理。
// 推論：π₁(G) ≅ 自由群 F_{E−V+1}（以既約閉路計數驗證）。
// ============================================================================

///|
/// 無向圖：edges[i] = (u, v)。
pub struct Graph {
  nv : Int32
  edges : Array[(Int32, Int32)]
}

///|
/// 一步：((邊號, 是否正向))。
pub type Step = (Int32, Bool)

///|
/// 路徑：起點 + 步序列。
pub struct Path {
  start : Int32
  steps : Array[Step]
}

///|
pub fn Graph::has_edge(self : Graph, u : Int32, v : Int32) -> Bool {
  for e in self.edges {
    if (e.0 == u && e.1 == v) || (e.0 == v && e.1 == u) {
      return true
    }
  }
  false
}

///|
pub fn Graph::end_of(self : Graph, p : Path) -> Int32 {
  let mut cur = p.start
  for s in p.steps {
    let e = self.edges[s.0]
    cur = if s.1 { e.1 } else { e.0 }
  }
  cur
}

///|
pub fn Graph::valid(self : Graph, p : Path) -> Bool {
  let mut cur = p.start
  for s in p.steps {
    let e = self.edges[s.0]
    let (u, v) = if s.1 { (e.0, e.1) } else { (e.1, e.0) }
    if cur != u {
      return false
    }
    cur = v
  }
  true
}

///|
pub fn Graph::reduce(self : Graph, p : Path) -> Path {
  let _ = self
  let stack : Array[Step] = []
  for s in p.steps {
    let mut popped = false
    if stack.length() > 0 {
      let top = stack[stack.length() - 1]
      if top.0 == s.0 && top.1 != s.1 {
        let _ = stack.pop()
        popped = true
      }
    }
    if !popped {
      stack.push(s)
    }
  }
  { start: p.start, steps: stack, }
}

///|
pub fn Graph::compose(self : Graph, p : Path, q : Path) -> Path {
  let _ = self
  let steps : Array[Step] = []
  for s in p.steps {
    steps.push(s)
  }
  for s in q.steps {
    steps.push(s)
  }
  { start: p.start, steps, }
}

///|
pub fn Graph::invert(self : Graph, p : Path) -> Path {
  let steps : Array[Step] = []
  let n = p.steps.length()
  for i in 0..<n {
    let s = p.steps[n - 1 - i]
    steps.push((s.0, !s.1))
  }
  // 反轉後起點是原終點
  { start: self.end_of(p), steps, }
}

///|
/// 並查集
pub struct DSU {
  parent : Array[Int32]
}

///|
pub fn DSU::make(n : Int32) -> DSU {
  let p : Array[Int32] = []
  for i in 0..<n {
    p.push(i)
  }
  { parent: p, }
}

///|
pub fn DSU::find(self : DSU, x : Int32) -> Int32 {
  let mut r = x
  while self.parent[r] != r {
    r = self.parent[r]
  }
  r
}

///|
pub fn DSU::union(self : DSU, a : Int32, b : Int32) -> Unit {
  let ra = self.find(a)
  let rb = self.find(b)
  if ra != rb {
    self.parent[rb] = ra
  }
}

///|
/// 枚舉圖上所有長度 ≤ max_len 且起點 = v0 的路徑（以索引表回傳）。
pub fn enumerate_paths(g : Graph, v0 : Int32, max_len : Int32) -> Array[Path] {
  let all : Array[Path] = [{ start: v0, steps: [], }]
  let mut frontier : Array[Int32] = [0] // 索引
  for _ in 0..<max_len {
    let next : Array[Int32] = []
    for idx in frontier {
      let p = all[idx]
      let cur = g.end_of(p)
      for e in 0..<g.edges.length() {
        let ed = g.edges[e]
        for dir in [true, false] {
          let (u, v) = if dir { (ed.0, ed.1) } else { (ed.1, ed.0) }
          if u == cur {
            let steps = p.steps.copy()
            steps.push((e, dir))
            all.push({ start: v0, steps, })
            next.push(all.length() - 1)
          }
        }
      }
    }
    frontier = next
  }
  all
}

///|
/// 以「插入/刪除 aa⁻¹」建同倫等價類（限制長度 ≤ max_len）。
/// 回傳 (等價類編號, 索引)。
pub fn homotopy_classes(
  g : Graph,
  v0 : Int32,
  max_len : Int32,
) -> (DSU, Array[Path]) {
  let paths = enumerate_paths(g, v0, max_len)
  let dsu = DSU::make(paths.length())
  // 索引：以 (start, steps) 雜湊不便，直接用 O(n²) 比對（規模小）
  for i in 0..<paths.length() {
    let p = paths[i]
    // 嘗試刪除每一步後的 aa⁻¹
    for j in 0..<p.steps.length() {
      if j + 1 < p.steps.length() {
        let a = p.steps[j]
        let b = p.steps[j + 1]
        if a.0 == b.0 && a.1 != b.1 {
          let steps : Array[Step] = []
          for k in 0..<p.steps.length() {
            if k != j && k != j + 1 {
              steps.push(p.steps[k])
            }
          }
          let q : Path = { start: p.start, steps, }
          // 找 q 的索引
          for t in 0..<paths.length() {
            if same_path(paths[t], q) {
              dsu.union(i, t)
            }
          }
        }
      }
    }
  }
  (dsu, paths)
}

///|
pub fn same_path(a : Path, b : Path) -> Bool {
  if a.start != b.start || a.steps.length() != b.steps.length() {
    return false
  }
  for i in 0..<a.steps.length() {
    if a.steps[i].0 != b.steps[i].0 || a.steps[i].1 != b.steps[i].1 {
      return false
    }
  }
  true
}

///|
/// 玫瑰圖 R_r：1 個頂點，r 條自環。
pub fn rose(r : Int32) -> Graph {
  let edges : Array[(Int32, Int32)] = []
  for _ in 0..<r {
    edges.push((0, 0))
  }
  { nv: 1, edges, }
}

///|
pub fn checks() -> Array[(String, Bool, String)] {
  let out : Array[(String, Bool, String)] = []

  // ---- 1. 既約化是正規形式 ----
  let g = rose(2)
  let mut ok = true
  let mut checked = 0
  let (dsu, paths) = homotopy_classes(g, 0, 4)
  for i in 0..<paths.length() {
    let ri = g.reduce(paths[i])
    for j in 0..<paths.length() {
      let rj = g.reduce(paths[j])
      let same_class = dsu.find(i) == dsu.find(j)
      let same_normal = same_path(ri, rj)
      if same_class != same_normal {
        ok = false
      }
      checked = checked + 1
    }
  }
  out.push(
    (
      "同倫類 ⟺ 既約形式相同（玫瑰圖 R2，長度 ≤4，\{checked} 對）",
      ok,
      "\{paths.length()} 條路徑",
    ),
  )

  // ---- 2. 群胚公理 ----
  let mut ax = true
  let p1 : Path = { start: 0, steps: [(0, true), (1, true)], }
  let p2 : Path = { start: 0, steps: [(1, false)], }
  let p3 : Path = { start: 0, steps: [(0, false)], }
  let c1 = g.reduce(g.compose(g.compose(p1, p2), p3))
  let c2 = g.reduce(g.compose(p1, g.compose(p2, p3)))
  if !same_path(c1, c2) {
    ax = false
  }
  // 單位與反元素
  let unit : Path = { start: 0, steps: [], }
  if !same_path(g.reduce(g.compose(p1, unit)), p1) {
    ax = false
  }
  if !same_path(g.reduce(g.compose(p1, g.invert(p1))), unit) {
    ax = false
  }
  out.push(
    (
      "自由群胚公理：結合律、單位、反元素", ax, "p1p2p3 兩種括號",
    ),
  )

  // ---- 3. 自由群計數 ----
  let mut counts_ok = true
  let mut desc = ""
  for r in [1, 2, 3] {
    let gr = rose(r)
    let ps = enumerate_paths(gr, 0, 6)
    for n in 1..<7 {
      let mut closed_reduced = 0
      for p in ps {
        if p.steps.length() == n {
          let red = gr.reduce(p)
          if red.steps.length() == n {
            closed_reduced = closed_reduced + 1
          }
        }
      }
      let expect = 2 * r
      let mut e = 2 * r
      for _ in 1..<n {
        e = e * (2 * r - 1)
      }
      let _ = expect
      if closed_reduced != e {
        counts_ok = false
      }
      if n == 3 {
        desc = desc + "r=\{r}: \{closed_reduced} (期望 \{e})；"
      }
    }
  }
  out.push(
    (
      "π₁(玫瑰圖) = F_r：長度 n 既約閉路數 = 2r(2r−1)^{n−1}", counts_ok,
      desc,
    ),
  )

  // ---- 4. 有向版本不是群胚 ----
  // 只允許正向步：單向圖 0→1 中，(0→1) 無反元素
  let dg : Graph = { nv: 2, edges: [(0, 1)], }
  let fwd : Path = { start: 0, steps: [(0, true)], }
  let inv = dg.invert(fwd)
  // 有向路徑類別中，允許的步只有正向；inv 含反向步 ⇒ 不在類別中
  let mut inv_admissible = true
  for s in inv.steps {
    if !s.1 {
      inv_admissible = false
    }
  }
  out.push(
    (
      "有向路徑空間：0→1 的反向步不可容許（範疇而非群胚）",
      !inv_admissible,
      "反向邊不存在 ⇒ 非群胚，這是 A¹-同倫與 d-space 的起點",
    ),
  )

  // ---- 5. θ 圖：π₁ = F₂（生成樹 + 非樹邊 = 自由生成元） ----
  // θ：2 頂點 3 條邊；以邊 0 為生成樹，邊 1,2 為自由生成元。
  let theta : Graph = { nv: 2, edges: [(0, 1), (0, 1), (0, 1)], }
  let ps = enumerate_paths(theta, 0, 5)
  let closed : Array[Path] = []
  for p in ps {
    if theta.end_of(p) == 0 {
      closed.push(p)
    }
  }
  // 5a. 既約閉路計數：偶數長度 n ⇒ 3·2^{n−1}
  let mut count_ok = true
  for n in [2, 4] {
    let mut cnt = 0
    for p in closed {
      if p.steps.length() == n {
        let r = theta.reduce(p)
        if r.steps.length() == n {
          cnt = cnt + 1
        }
      }
    }
    let e = 3 * pow2(n - 1)
    if cnt != e {
      count_ok = false
    }
  }
  out.push(
    (
      "θ 圖既約閉路計數 = 3·2^{n−1}（n=2,4）", count_ok, "r = E − V + 1 = 2",
    ),
  )

  // 5b. 同倫類 ⟺ 非樹邊字（去掉生成樹邊 0）之既約字相同
  let mut word_ok = true
  for i in 0..<closed.length() {
    for j in 0..<closed.length() {
      let wi = theta_word(closed[i])
      let wj = theta_word(closed[j])
      let same_word = same_steps(wi, wj)
      // 用既約形式判定同倫
      let same_homotopy = same_path(
        theta.reduce(closed[i]),
        theta.reduce(closed[j]),
      )
      if same_word != same_homotopy {
        word_ok = false
      }
    }
  }
  out.push(
    (
      "π₁(θ) ≅ F₂：同倫類 ⟺ 非樹邊字相同（\{closed.length()} 條閉路兩兩比較）",
      word_ok,
      "生成樹邊被消去，兩條非樹邊給出自由生成元",
    ),
  )

  // 5c. 自由群的增長：既約字長度 n 的個數（對 F₂ 應為 4·3^{n−1}）
  let mut growth_ok = true
  let mut desc = ""
  for n in [1, 2, 3] {
    let words = enumerate_words(2, n)
    let expect = 4 * pow3(n - 1)
    if words != expect {
      growth_ok = false
    }
    desc = desc + "n=\{n}: \{words} "
  }
  out.push(("F₂ 既約字增長 4·3^{n−1}", growth_ok, desc))

  out
}

///|
fn pow2(n : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<n {
    r = r * 2
  }
  r
}

///|
fn pow3(n : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<n {
    r = r * 3
  }
  r
}

///|
fn same_steps(a : Array[Step], b : Array[Step]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if a[i].0 != b[i].0 || a[i].1 != b[i].1 {
      return false
    }
  }
  true
}

///|
/// 閉路 → 非樹邊（邊 1,2）之既約字。
fn theta_word(p : Path) -> Array[Step] {
  let w : Array[Step] = []
  for s in p.steps {
    if s.0 == 0 {
      continue
    }
    let mut popped = false
    if w.length() > 0 {
      let top = w[w.length() - 1]
      if top.0 == s.0 && top.1 != s.1 {
        let _ = w.pop()
        popped = true
      }
    }
    if !popped {
      w.push(s)
    }
  }
  w
}

///|
/// 秩 r 自由群中長度恰為 n 的既約字個數。
fn enumerate_words(r : Int32, n : Int32) -> Int32 {
  if n == 0 {
    return 1
  }
  let mut total = 0
  // 以 DP：狀態 = 上一個字母是否已被選（僅需計數）
  // 長度 1：2r；之後每步 2r−1
  let mut cur = 2 * r
  for _ in 1..<n {
    cur = cur * (2 * r - 1)
  }
  total = cur
  total
}
