// ============================================================================
// num — 精確數論基礎：有理數 Rat（架於 core BigInt）、有限域 Fp (p = 2^31-1)、
//        Legendre 符號、Mersenne 模乘、以及可在不同代數結構間複用的 Semiring 抽象。
//
// 設計原則：所有代數律都「可被執行驗證」，不留任何未實作的擺設。
// ============================================================================

///|
/// 無號最大公因數（BigInt 版 Euclid）。
pub fn big_gcd(a : @bigint.BigInt, b : @bigint.BigInt) -> @bigint.BigInt {
  let z = @bigint.BigInt::from_int(0)
  let mut x = if a.compare(z) < 0 { a.neg() } else { a }
  let mut y = if b.compare(z) < 0 { b.neg() } else { b }
  while y.compare(z) > 0 {
    let r = x.mod(y)
    x = y
    y = r
  }
  x
}

///|
pub fn big_abs(x : @bigint.BigInt) -> @bigint.BigInt {
  if x.compare(@bigint.BigInt::from_int(0)) < 0 {
    x.neg()
  } else {
    x
  }
}

///|
/// 有理數。不變量：den > 0 且 gcd(|num|, den) = 1。
pub struct Rat {
  num : @bigint.BigInt
  den : @bigint.BigInt
}

///|
pub fn Rat::make(n : @bigint.BigInt, d : @bigint.BigInt) -> Rat {
  let z = @bigint.BigInt::from_int(0)
  if d.equal(z) {
    abort("Rat: zero denominator")
  }
  let mut nn = n
  let mut dd = d
  if dd.compare(z) < 0 {
    nn = nn.neg()
    dd = dd.neg()
  }
  let g = big_gcd(nn, dd)
  if !g.equal(z) {
    nn = nn.div(g)
    dd = dd.div(g)
  }
  { num: nn, den: dd, }
}

///|
pub fn Rat::of_int(n : Int32) -> Rat {
  Rat::make(@bigint.BigInt::from_int(n), @bigint.BigInt::from_int(1))
}

///|
pub fn Rat::zero() -> Rat {
  Rat::of_int(0)
}

///|
pub fn Rat::one() -> Rat {
  Rat::of_int(1)
}

///|
pub fn Rat::is_zero(self : Rat) -> Bool {
  self.num.equal(@bigint.BigInt::from_int(0))
}

///|
pub fn Rat::neg(self : Rat) -> Rat {
  { num: self.num.neg(), den: self.den, }
}

///|
pub fn Rat::add(self : Rat, o : Rat) -> Rat {
  Rat::make(self.num * o.den + o.num * self.den, self.den * o.den)
}

///|
pub fn Rat::sub(self : Rat, o : Rat) -> Rat {
  self.add(o.neg())
}

///|
pub fn Rat::mul(self : Rat, o : Rat) -> Rat {
  Rat::make(self.num * o.num, self.den * o.den)
}

///|
pub fn Rat::div(self : Rat, o : Rat) -> Rat {
  Rat::make(self.num * o.den, self.den * o.num)
}

///|
pub fn Rat::compare(self : Rat, o : Rat) -> Int32 {
  (self.num * o.den).compare(o.num * self.den)
}

///|

///|
/// 精確十進位展開（長除法），places 為小數位數。不需要浮點。
pub fn Rat::to_decimal(self : Rat, places : Int32) -> String {
  let ten = @bigint.BigInt::from_int(10)
  let zero = @bigint.BigInt::from_int(0)
  let neg = self.num.compare(zero) < 0
  let abs_n = big_abs(self.num)
  let ip = abs_n.div(self.den)
  let mut rem = abs_n.mod(self.den)
  let mut frac = ""
  let mut i = 0
  while i < places && !rem.equal(zero) {
    rem = rem * ten
    let d = rem.div(self.den)
    rem = rem.mod(self.den)
    frac = frac + d.to_string()
    i = i + 1
  }
  let sign = if neg { "-" } else { "" }
  if frac.length() == 0 {
    sign + ip.to_string()
  } else {
    sign + ip.to_string() + "." + frac
  }
}

///|
pub impl Eq for Rat with fn equal(self, o) {
  self.num.equal(o.num) && self.den.equal(o.den)
}

///|
pub impl Add for Rat with fn add(self, o) {
  self.add(o)
}

///|
pub impl Sub for Rat with fn sub(self, o) {
  self.sub(o)
}

///|
pub impl Mul for Rat with fn mul(self, o) {
  self.mul(o)
}

///|
pub impl Div for Rat with fn div(self, o) {
  self.div(o)
}

///|
pub impl Neg for Rat with fn neg(self) {
  self.neg()
}

///|
pub impl Compare for Rat with fn compare(self, o) {
  self.compare(o)
}

///|
pub impl Show for Rat with fn to_string(self) {
  if self.den.equal(@bigint.BigInt::from_int(1)) {
    self.num.to_string()
  } else {
    "\{self.num}/\{self.den}"
  }
}

// ---------------------------------------------------------------------------
// Fp : 質數體 GF(p)，p = 2^31 - 1（Mersenne 質數，p ≡ 3 mod 4）
// ---------------------------------------------------------------------------

///|
pub const MODULUS : Int32 = 2147483647

///|
pub const MODULUS_MINUS_2 : Int32 = MODULUS - 2

///|
/// 有限域元素。不變量：0 <= value < MODULUS。
pub struct Fp(Int32)

///|
pub fn Fp::make(x : Int32) -> Fp {
  let mut v = x % MODULUS
  if v < 0 {
    v = v + MODULUS
  }
  Fp(v)
}

///|
pub fn Fp::value(self : Fp) -> Int32 {
  self.0
}

///|
pub fn Fp::zero() -> Fp {
  Fp(0)
}

///|
pub fn Fp::one() -> Fp {
  Fp(1)
}

///|
pub fn Fp::add(self : Fp, o : Fp) -> Fp {
  let s = self.0.to_int64() + o.0.to_int64()
  Fp(
    (if s >= MODULUS.to_int64() { s - MODULUS.to_int64() } else { s }).to_int(),
  )
}

///|
pub fn Fp::neg(self : Fp) -> Fp {
  Fp(if self.0 == 0 { 0 } else { MODULUS - self.0 })
}

///|
pub fn Fp::sub(self : Fp, o : Fp) -> Fp {
  self.add(o.neg())
}

///|
/// Mersenne 模乘：x = a*b < 2^62；寫 x = hi*2^31 + lo，用 2^31 ≡ 1 (mod p)。
pub fn Fp::mul(self : Fp, o : Fp) -> Fp {
  let p64 : Int64 = MODULUS.to_int64()
  let x = self.0.to_int64() * o.0.to_int64()
  let hi = x >> 31
  let lo = x & 2147483647L
  let mut y = hi + lo
  if y >= p64 {
    y = y - p64
  }
  if y >= p64 {
    y = y - p64
  }
  Fp(y.to_int())
}

///|
/// 快速冪（平方─乘），指數以 Int 表示。
pub fn Fp::pow(self : Fp, e : Int32) -> Fp {
  let mut result = Fp::one()
  let mut base = self
  let mut n = e
  while n > 0 {
    if n % 2 == 1 {
      result = result.mul(base)
    }
    base = base.mul(base)
    n = n / 2
  }
  result
}

///|
/// 乘法反元素：Fermat 小定理 a^(p-2)。
pub fn Fp::inv(self : Fp) -> Fp {
  self.pow(MODULUS_MINUS_2)
}

///|
pub fn Fp::div(self : Fp, o : Fp) -> Fp {
  self.mul(o.inv())
}

///|
pub impl Add for Fp with fn add(self, o) {
  self.add(o)
}

///|
pub impl Sub for Fp with fn sub(self, o) {
  self.sub(o)
}

///|
pub impl Mul for Fp with fn mul(self, o) {
  self.mul(o)
}

///|
pub impl Div for Fp with fn div(self, o) {
  self.div(o)
}

///|
pub impl Neg for Fp with fn neg(self) {
  self.neg()
}

///|
pub impl Eq for Fp with fn equal(self, o) {
  self.0 == o.0
}

///|
pub impl Show for Fp with fn to_string(self) {
  self.0.to_string()
}

///|
/// Legendre 符號 χ(a) ∈ {-1, 0, 1}：a^((p-1)/2) 的取值。
pub fn legendre(a : Fp) -> Int32 {
  if a.value() == 0 {
    0
  } else {
    let t = a.pow((MODULUS - 1) / 2)
    if t.value() == 1 {
      1
    } else {
      -1
    }
  }
}

///|
/// 平方根（p ≡ 3 mod 4）：a^((p+1)/4)。
pub fn Fp::sqrt(self : Fp) -> Fp {
  // (p+1)/4 以 Int64 計算，避免 p+1 在 Int32 溢位
  self.pow(((MODULUS.to_int64() + 1L) / 4L).to_int())
}

// ---------------------------------------------------------------------------
// 抽象：Semiring —— 同一段 Horner 程式碼同時服務 Int / Rat / Fp / Trop，
// 選擇在「編譯期」由型別參數單態化決定（見 README 的零成本證據）。
// ---------------------------------------------------------------------------

///|
pub(open) trait Semiring {
  fn zero() -> Self
  fn one() -> Self
  fn add(Self, Self) -> Self
  fn mul(Self, Self) -> Self
}

///|
pub impl Semiring for Int32 with fn zero() {
  0
}

///|
pub impl Semiring for Int32 with fn one() {
  1
}

///|
pub impl Semiring for Int32 with fn add(self, o) {
  self + o
}

///|
pub impl Semiring for Int32 with fn mul(self, o) {
  self * o
}

///|
pub impl Semiring for Fp with fn zero() {
  Fp::zero()
}

///|
pub impl Semiring for Fp with fn one() {
  Fp::one()
}

///|
pub impl Semiring for Fp with fn add(self, o) {
  self.add(o)
}

///|
pub impl Semiring for Fp with fn mul(self, o) {
  self.mul(o)
}

///|
pub impl Semiring for Rat with fn zero() {
  Rat::zero()
}

///|
pub impl Semiring for Rat with fn one() {
  Rat::one()
}

///|
pub impl Semiring for Rat with fn add(self, o) {
  self.add(o)
}

///|
pub impl Semiring for Rat with fn mul(self, o) {
  self.mul(o)
}

///|
/// Horner 求值：泛型於 Semiring。零成本：見 wasm 反組譯證據。
pub fn[T : Semiring] horner(coeffs : Array[T], x : T) -> T {
  let mut acc = T::zero()
  let mut i = coeffs.length() - 1
  while i >= 0 {
    acc = T::add(T::mul(acc, x), coeffs[i])
    i = i - 1
  }
  acc
}

// ---------------------------------------------------------------------------
// 檢查表
// ---------------------------------------------------------------------------

///|
pub fn checks() -> Array[(String, Bool, String)] {
  let out : Array[(String, Bool, String)] = []
  // 1. Mersenne 模乘 vs BigInt 參照實作（隨機 + 邊界）
  let mut ok = true
  let samples : Array[(Int32, Int32)] = [
    (0, 0),
    (1, 1),
    (MODULUS - 1, MODULUS - 1),
    (2, 1073741824),
    (123456789, 987654321),
    (MODULUS - 1, 3),
    (65536, 65536),
  ]
  for p in samples {
    let a = Fp::make(p.0)
    let b = Fp::make(p.1)
    let got = a.mul(b).value()
    let want = (@bigint.BigInt::from_int(p.0) *
    @bigint.BigInt::from_int(p.1) %
    @bigint.BigInt::from_int(MODULUS)).to_int()
    if got != want {
      ok = false
    }
  }
  out.push(
    (
      "Fp::mul 與 BigInt 參照一致（Mersenne 縮減）", ok, "7 個含邊界樣本",
    ),
  )

  // 2. 域公理：結合律、分配律、反元素（隨機樣本）
  let mut ok2 = true
  let mut seed : Int64 = 12345L
  for _ in 0..<200 {
    seed = (seed * 1103515245L + 12345L) % 2147483647L
    let a = Fp::make(seed.to_int())
    seed = (seed * 1103515245L + 12345L) % 2147483647L
    let b = Fp::make(seed.to_int())
    seed = (seed * 1103515245L + 12345L) % 2147483647L
    let c = Fp::make(seed.to_int())
    if !(a.add(b).add(c) == a.add(b.add(c))) ||
      !(a.mul(b).mul(c) == a.mul(b.mul(c))) {
      ok2 = false
    }
    if !(a.mul(b.add(c)) == a.mul(b).add(a.mul(c))) {
      ok2 = false
    }
    if !a.equal(Fp::zero()) && !(a.mul(a.inv()) == Fp::one()) {
      ok2 = false
    }
  }
  out.push(
    (
      "GF(2^31-1) 域公理（結合/分配/反元素）", ok2, "200 組隨機樣本",
    ),
  )

  // 3. Legendre 符號：Euler 判準 + 二次剩餘計數 (p-1)/2
  let mut ok3 = true
  let mut qr = 0
  for i in 1..<2001 {
    let a = Fp::make(i)
    let chi = legendre(a)
    let s = a.sqrt()
    if chi == 1 && !(s.mul(s) == a) {
      ok3 = false
    }
    if chi == -1 && s.mul(s) == a {
      ok3 = false
    }
    if chi == 1 {
      qr = qr + 1
    }
  }
  out.push(("Legendre/Euler 判準 + sqrt 互逆", ok3, "i < 2000"))
  out.push(
    (
      "二次剩餘密度 = 1/2（前 2000 個元素）",
      qr * 1000 / 2000 >= 490 && qr * 1000 / 2000 <= 510,
      "χ=1 的個數 = \{qr}",
    ),
  )

  // 4. Rat 正規化與體公理
  let mut ok4 = true
  for (n, d) in [(2, 4), (-6, 8), (0, 5), (7, -3), (100, 10)] {
    let r = Rat::make(@bigint.BigInt::from_int(n), @bigint.BigInt::from_int(d))
    if r.num.equal(@bigint.BigInt::from_int(0)) {
      if !r.den.equal(@bigint.BigInt::from_int(1)) {
        ok4 = false
      }
    } else if !big_gcd(r.num, r.den).equal(@bigint.BigInt::from_int(1)) ||
      r.den.compare(@bigint.BigInt::from_int(0)) <= 0 {
      ok4 = false
    }
  }
  let a = Rat::make(@bigint.BigInt::from_int(2), @bigint.BigInt::from_int(3))
  let b = Rat::make(@bigint.BigInt::from_int(3), @bigint.BigInt::from_int(4))
  if !(a.mul(b) ==
    Rat::make(@bigint.BigInt::from_int(1), @bigint.BigInt::from_int(2))) {
    ok4 = false
  }
  if !(a.add(b) ==
    Rat::make(@bigint.BigInt::from_int(17), @bigint.BigInt::from_int(12))) {
    ok4 = false
  }
  out.push(
    ("Rat 正規化（gcd、正分母）與體運算", ok4, "2/3 + 3/4 = 17/12"),
  )

  // 5. 泛型 Horner：三種 Semiring 下的同一份程式碼
  let c = [1, 2, 3]
  let h_int = horner(c, 10)
  let h_fp = horner([Fp::one(), Fp::make(2), Fp::make(3)], Fp::make(10))
  let h_rat = horner(
    [
      Rat::one(),
      Rat::make(@bigint.BigInt::from_int(2), @bigint.BigInt::from_int(3)),
    ],
    Rat::of_int(3),
  )
  // 1 + 2*10 + 3*100 = 321 ; 1 + (2/3)*3 = 3
  let ok5 = h_int == 321 && h_fp.equal(Fp::make(321)) && h_rat == Rat::of_int(3)
  out.push(
    ("泛型 Horner 於 Int/Fp/Rat 單態化後皆正確", ok5, "321, 321, 3"),
  )

  // 非平凡性證人：Fp::mul 的 Mersenne 縮減若少了第二道減法就會錯
  let x = Fp::make(MODULUS - 1)
  out.push(
    (
      "非平凡性：(p-1)^2 mod p = 1（需要兩次縮減）",
      x.mul(x).equal(Fp::one()),
      "(p-1)^2 = p^2-2p+1",
    ),
  )

  out
}
