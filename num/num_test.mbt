// num 的單元測試：精確有理數與有限體的基本恆等式（非恆真斷言）。

///|
test "rat: 1/2 + 1/3 = 5/6" {
  let a = Rat::make(@bigint.BigInt::from_int(1), @bigint.BigInt::from_int(2))
  let b = Rat::make(@bigint.BigInt::from_int(1), @bigint.BigInt::from_int(3))
  let c = Rat::make(@bigint.BigInt::from_int(5), @bigint.BigInt::from_int(6))
  assert_eq(a.add(b).compare(c), 0)
}

///|
test "rat: 歸一化 2/4 = 1/2" {
  let a = Rat::make(@bigint.BigInt::from_int(2), @bigint.BigInt::from_int(4))
  let b = Rat::make(@bigint.BigInt::from_int(1), @bigint.BigInt::from_int(2))
  assert_eq(a.compare(b), 0)
}

///|
test "fp: 費馬小定理 a^(p−1) = 1" {
  let a = Fp::make(12)
  assert_eq(a.pow(MODULUS - 1).value(), 1)
}

///|
test "fp: 4 是二次剩餘、χ(4) = 1" {
  assert_eq(legendre(Fp::make(4)), 1)
}

///|
test "fp: 歐拉判準 χ(a) ≡ a^((p−1)/2)（對 a = 5 檢查）" {
  let a = Fp::make(5)
  let e = a.pow((MODULUS - 1) / 2).value()
  let chi = legendre(a)
  // χ = 1 ⟺ a^((p−1)/2) = 1；χ = −1 ⟺ = p − 1
  assert_eq(if chi == 1 { 1 } else { MODULUS - 1 }, e)
}
