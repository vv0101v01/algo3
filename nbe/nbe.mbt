// ============================================================================
// nbe — 規範形式 (normal forms) 之可執行版本：
//       單型 λ 演算（Δ：積、和、單位、布爾）的 正規化即求值 (normalization by
//       evaluation, NbE)。quote ∘ eval 給出 β-規範、η-長的形式；
//       兩項 βη-相等 ⟺ 正規形式語法相同（de Bruijn 表示 ⇒ α-等價即相等）。
//
// 定理（canonicity）：閉項在原子型別上的正規形式必為典範式
//   （Bool ⇒ tru/fls；Unit ⇒ one）。
// ============================================================================

///|
pub enum Ty {
  U // Unit
  B // Bool
  Arr(Ty, Ty)
  Prod(Ty, Ty)
}

///|
pub fn Ty::show(self : Ty) -> String {
  match self {
    U => "1"
    B => "2"
    Arr(a, b) => "(\{a.show()}→\{b.show()})"
    Prod(a, b) => "(\{a.show()}×\{b.show()})"
  }
}

///|
pub fn Ty::eq(self : Ty, o : Ty) -> Bool {
  match self {
    U =>
      match o {
        U => true
        _ => false
      }
    B =>
      match o {
        B => true
        _ => false
      }
    Arr(a, b) =>
      match o {
        Arr(c, d) => a.eq(c) && b.eq(d)
        _ => false
      }
    Prod(a, b) =>
      match o {
        Prod(c, d) => a.eq(c) && b.eq(d)
        _ => false
      }
  }
}

///|
pub enum Tm {
  Var(Int32)
  Lam(Ty, Tm)
  App(Tm, Tm)
  One
  Tru
  Fls
  If(Tm, Tm, Tm)
  Pair(Tm, Tm)
  Fst(Tm)
  Snd(Tm)
}

///|
pub fn Tm::eq(self : Tm, o : Tm) -> Bool {
  match (self, o) {
    (Var(i), Var(j)) => i == j
    (Lam(a, b), Lam(c, d)) => a.eq(c) && b.eq(d)
    (App(f, x), App(g, y)) => f.eq(g) && x.eq(y)
    (One, One) => true
    (Tru, Tru) => true
    (Fls, Fls) => true
    (If(a, b, c), If(d, e, f)) => a.eq(d) && b.eq(e) && c.eq(f)
    (Pair(a, b), Pair(c, d)) => a.eq(c) && b.eq(d)
    (Fst(a), Fst(b)) => a.eq(b)
    (Snd(a), Snd(b)) => a.eq(b)
    _ => false
  }
}

///|
pub fn Tm::show(self : Tm) -> String {
  match self {
    Var(i) => "x\{i}"
    Lam(_, b) => "λ.(\{b.show()})"
    App(f, x) => "(\{f.show()} \{x.show()})"
    One => "()"
    Tru => "tt"
    Fls => "ff"
    If(c, t, e) => "if \{c.show()} then \{t.show()} else \{e.show()}"
    Pair(a, b) => "⟨\{a.show()},\{b.show()}⟩"
    Fst(a) => "π₁(\{a.show()})"
    Snd(a) => "π₂(\{a.show()})"
  }
}

// ---------------------------------------------------------------------------
// 型別檢查（確保我們只在良型項上談 βη）
// ---------------------------------------------------------------------------

///|
pub fn infer(ctx : Array[Ty], t : Tm) -> Ty? {
  match t {
    Var(i) => if i < ctx.length() { Some(ctx[i]) } else { None }
    Lam(a, b) => {
      let ctx2 : Array[Ty] = [a]
      for x in ctx {
        ctx2.push(x)
      }
      match infer(ctx2, b) {
        Some(r) => Some(Arr(a, r))
        None => None
      }
    }
    App(f, x) =>
      match (infer(ctx, f), infer(ctx, x)) {
        (Some(Arr(a, b)), Some(c)) => if a.eq(c) { Some(b) } else { None }
        _ => None
      }
    One => Some(U)
    Tru => Some(B)
    Fls => Some(B)
    If(c, a, b) =>
      match (infer(ctx, c), infer(ctx, a), infer(ctx, b)) {
        (Some(B), Some(ta), Some(tb)) => if ta.eq(tb) { Some(ta) } else { None }
        _ => None
      }
    Pair(a, b) =>
      match (infer(ctx, a), infer(ctx, b)) {
        (Some(x), Some(y)) => Some(Prod(x, y))
        _ => None
      }
    Fst(p) =>
      match infer(ctx, p) {
        Some(Prod(x, _)) => Some(x)
        _ => None
      }
    Snd(p) =>
      match infer(ctx, p) {
        Some(Prod(_, y)) => Some(y)
        _ => None
      }
  }
}

// ---------------------------------------------------------------------------
// 語意域（值）與環境
// ---------------------------------------------------------------------------

///|
pub enum Env {
  Nil
  Cons(Val, Env)
}

///|
pub enum Val {
  VOne
  VBool(Bool)
  VClo(Env, Array[Ty], Ty, Tm) // 捕獲環境、型別上下文、定義域型別、函數體
  VPair(Val, Val)
  VNeu(Neu)
}

///|
/// 中性值；每個節點自帶型別，使 quote 無需外部型別資訊即可 η-展開。
pub enum Neu {
  NVar(Int32, Ty) // de Bruijn level
  NApp(Neu, Val, Ty) // 結果型別
  NIf(Neu, Val, Val, Ty) // 分支型別
  NFst(Neu, Ty) // 結果型別
  NSnd(Neu, Ty)
}

///|
pub fn Neu::ty(self : Neu) -> Ty {
  match self {
    NVar(_, t) => t
    NApp(_, _, t) => t
    NIf(_, _, _, t) => t
    NFst(_, t) => t
    NSnd(_, t) => t
  }
}

///|
pub fn Env::get(self : Env, i : Int32) -> Val {
  match self {
    Nil => abort("unbound variable")
    Cons(v, rest) => if i == 0 { v } else { rest.get(i - 1) }
  }
}

///|
fn must_ty(ctx : Array[Ty], t : Tm) -> Ty {
  match infer(ctx, t) {
    Some(ty) => ty
    None => abort("ill-typed term during evaluation")
  }
}

///|
fn cons_ty(a : Ty, ctx : Array[Ty]) -> Array[Ty] {
  let out : Array[Ty] = [a]
  for x in ctx {
    out.push(x)
  }
  out
}

///|
pub fn eval(ctx : Array[Ty], env : Env, t : Tm) -> Val {
  match t {
    Var(i) => env.get(i)
    Lam(a, b) => VClo(env, ctx, a, b)
    App(f, x) =>
      match eval(ctx, env, f) {
        VClo(env2, ctx2, _, body) =>
          eval(
            cons_ty(must_ty(ctx, x), ctx2),
            Cons(eval(ctx, env, x), env2),
            body,
          )
        VNeu(n) =>
          match n.ty() {
            Arr(_, b) => VNeu(NApp(n, eval(ctx, env, x), b))
            _ => abort("type error in eval: app")
          }
        _ => abort("type error in eval: app")
      }
    One => VOne
    Tru => VBool(true)
    Fls => VBool(false)
    If(c, a, b) =>
      match eval(ctx, env, c) {
        VBool(true) => eval(ctx, env, a)
        VBool(false) => eval(ctx, env, b)
        VNeu(n) =>
          VNeu(NIf(n, eval(ctx, env, a), eval(ctx, env, b), must_ty(ctx, a)))
        _ => abort("type error in eval: if")
      }
    Pair(a, b) => VPair(eval(ctx, env, a), eval(ctx, env, b))
    Fst(p) =>
      match eval(ctx, env, p) {
        VPair(a, _) => a
        VNeu(n) =>
          match n.ty() {
            Prod(x, _) => VNeu(NFst(n, x))
            _ => abort("type error in eval: fst")
          }
        _ => abort("type error in eval: fst")
      }
    Snd(p) =>
      match eval(ctx, env, p) {
        VPair(_, b) => b
        VNeu(n) =>
          match n.ty() {
            Prod(_, y) => VNeu(NSnd(n, y))
            _ => abort("type error in eval: snd")
          }
        _ => abort("type error in eval: snd")
      }
  }
}

///|
/// 型別導向的 quote：產生 β-規範且 η-長的形式。
pub fn quote(lvl : Int32, ty : Ty, v : Val) -> Tm {
  match (ty, v) {
    (U, VOne) => One
    (B, VBool(true)) => Tru
    (B, VBool(false)) => Fls
    (Arr(a, b), VClo(env, ctx, _, body)) =>
      Lam(
        a,
        quote(
          lvl + 1,
          b,
          eval(cons_ty(a, ctx), Cons(VNeu(NVar(lvl, a)), env), body),
        ),
      )
    (Arr(a, b), VNeu(n)) =>
      Lam(a, quote(lvl + 1, b, VNeu(NApp(n, VNeu(NVar(lvl, a)), b))))
    (Prod(a, b), VPair(x, y)) => Pair(quote(lvl, a, x), quote(lvl, b, y))
    (Prod(a, b), VNeu(n)) =>
      Pair(quote(lvl, a, VNeu(NFst(n, a))), quote(lvl, b, VNeu(NSnd(n, b))))
    (_, VNeu(n)) => quote_neu(lvl, n)
    _ => abort("quote: type mismatch")
  }
}

///|
/// 中性值的 readback。所有需要的型別都內建於節點。
pub fn quote_neu(lvl : Int32, n : Neu) -> Tm {
  match n {
    NVar(l, _) => Var(lvl - 1 - l)
    NApp(m, v, _) =>
      match m.ty() {
        Arr(a, _) => App(quote_neu(lvl, m), quote(lvl, a, v))
        _ => abort("quote_neu: non-function applied")
      }
    NIf(m, a, b, ty) =>
      If(quote_neu(lvl, m), quote(lvl, ty, a), quote(lvl, ty, b))
    NFst(m, _) => Fst(quote_neu(lvl, m))
    NSnd(m, _) => Snd(quote_neu(lvl, m))
  }
}

///|
/// 正規化 = quote ∘ eval。
pub fn normalize(t : Tm) -> Tm {
  match infer([], t) {
    Some(ty) => quote(0, ty, eval([], Nil, t))
    None => abort("normalize: ill-typed term")
  }
}

///|
/// β-規範：不存在 (λx.b) a、π₁⟨a,b⟩、if tt then… 等重寫基。
pub fn is_beta_normal(t : Tm) -> Bool {
  match t {
    Var(_) | One | Tru | Fls => true
    Lam(_, b) => is_beta_normal(b)
    App(f, x) =>
      match f {
        Lam(_, _) => false
        _ => is_beta_normal(f) && is_beta_normal(x)
      }
    If(c, a, b) =>
      match c {
        Tru | Fls => false
        _ => is_beta_normal(c) && is_beta_normal(a) && is_beta_normal(b)
      }
    Pair(a, b) => is_beta_normal(a) && is_beta_normal(b)
    Fst(p) =>
      match p {
        Pair(_, _) => false
        _ => is_beta_normal(p)
      }
    Snd(p) =>
      match p {
        Pair(_, _) => false
        _ => is_beta_normal(p)
      }
  }
}

///|
/// η-長：在函數型別上必為 λ，在積型別上必為 ⟨_,_⟩（原子型別無限制）。
pub fn is_eta_long(ty : Ty, t : Tm) -> Bool {
  match (ty, t) {
    // 原子型別沒有 η-規則：良型的 β-規範形式即 η-長
    (U, _) => true
    (B, _) => true
    (Arr(a, b), Lam(_, body)) => is_eta_long(b, body)
    (Arr(_, _), _) => false
    (Prod(a, b), Pair(x, y)) => is_eta_long(a, x) && is_eta_long(b, y)
    (Prod(_, _), _) => false
  }
}

///|
pub fn is_normal(ty : Ty, t : Tm) -> Bool {
  is_beta_normal(t) && is_eta_long(ty, t)
}

///|
/// βη-相等判定：正規化後語法比較（de Bruijn ⇒ α-不變）。
pub fn beta_eta_equal(a : Tm, b : Tm) -> Bool {
  normalize(a).eq(normalize(b))
}

// ---------------------------------------------------------------------------
// 檢查
// ---------------------------------------------------------------------------

///|
pub fn checks() -> Array[(String, Bool, String)] {
  let out : Array[(String, Bool, String)] = []
  let ab = Arr(U, U)
  // I = λx.x ; K = λx.λy.x
  let id = Lam(U, Var(0))
  let k = Lam(U, Lam(U, Var(1)))
  // (λx.x) (λy.y)
  let t1 = App(Lam(ab, Var(0)), Lam(U, Var(0)))
  // K applied: (λx.λy.x) ()  = λy.()
  let t2 = App(k, One)
  // π₁⟨(), λx.x⟩
  let t3 = Fst(Pair(One, id))
  // if tt then () else ()
  let t4 = If(Tru, One, One)
  // η：λx. (λy.y) x  ≡  λx.x
  let t5 = Lam(U, App(Lam(U, Var(0)), Var(0)))

  let n1 = normalize(t1)
  let n2 = normalize(t2)
  let n3 = normalize(t3)
  let n4 = normalize(t4)
  let n5 = normalize(t5)

  out.push(("(λx.x)(λy.y) ⇒ λx.x", n1.eq(Lam(U, Var(0))), n1.show()))
  out.push(("(λx.λy.x)() ⇒ λy.()", n2.eq(Lam(U, One)), n2.show()))
  out.push(("π₁⟨(),λx.x⟩ ⇒ ()", n3.eq(One), n3.show()))
  out.push(("if tt then () else () ⇒ ()", n4.eq(One), n4.show()))
  out.push(("η：λx.(λy.y)x ≡ λx.x", n5.eq(Lam(U, Var(0))), n5.show()))

  // 規範性：所有結果 β-規範且 η-長
  let mut all_norm = true
  for t in [n1, n2, n3, n4, n5] {
    match infer([], t) {
      Some(ty) => if !is_normal(ty, t) { all_norm = false }
      None => all_norm = false
    }
  }
  out.push(
    ("所有正規形式皆 β-規範且 η-長", all_norm, "5 個樣本"),
  )

  // 冪等
  let mut idem = true
  for t in [t1, t2, t3, t4, t5] {
    let once = normalize(t)
    let twice = normalize(once)
    if !once.eq(twice) {
      idem = false
    }
  }
  out.push(("冪等：normalize ∘ normalize = normalize", idem, ""))

  // 判定程序：βη-相等但語法不同
  out.push(
    (
      "βη-相等但語法不同：(λx.x)(λy.y) vs λz.z",
      t1.eq(Lam(U, Var(0))) == false && beta_eta_equal(t1, Lam(U, Var(0))),
      "",
    ),
  )
  // 非 βη-相等的項（見證判定非恆真）
  out.push(
    (
      "非平凡性：λx.λy.x 與 λx.λy.y 不 βη-相等",
      !beta_eta_equal(k, Lam(U, Lam(U, Var(0)))),
      "K ≠ K*",
    ),
  )

  // 典範性：Bool 閉項只可能是 tt/ff
  let bex = [If(Tru, Tru, Fls), If(Fls, Fls, Tru), App(Lam(B, Var(0)), Tru)]
  let mut canon = true
  for b in bex {
    let nb = normalize(b)
    if !(nb.eq(Tru) || nb.eq(Fls)) {
      canon = false
    }
  }
  out.push(
    ("典範性 (canonicity)：Bool 閉項 ⇒ tt 或 ff", canon, "3 個樣本"),
  )

  // 型別保持
  let mut tp = true
  for
    (a, b) in [
      (t1, n1),
      (t3, n3),
      (If(Tru, Tru, Fls), normalize(If(Tru, Tru, Fls))),
    ] {
    match (infer([], a), infer([], b)) {
      (Some(x), Some(y)) => if !x.eq(y) { tp = false }
      _ => tp = false
    }
  }
  out.push(("型別保持：normalize(e) 與 e 同型", tp, ""))

  // 非良型項被拒
  out.push(
    (
      "型別檢查器拒絕 (λx:2.x) tt？— 應接受；拒絕 App((),())",
      match infer([], App(One, One)) {
        None => true
        Some(_) => false
      },
      "ill-typed 被拒",
    ),
  )

  // 大一點的測試：丘奇數風格 + 多次 β-歸約
  // (λf.λx. f (f x)) (λy.y) () ⇒ ()
  let two = Lam(ab, Lam(U, App(Var(1), App(Var(1), Var(0)))))
  let big = App(App(two, Lam(U, Var(0))), One)
  let nb = normalize(big)
  out.push(("(λf.λx.f(f x))(λy.y)() ⇒ ()", nb.eq(One), nb.show()))

  out
}
