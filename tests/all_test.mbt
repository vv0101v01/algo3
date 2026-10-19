// 整合測試：所有套件的 checks() 必須全部通過，且檢查總數不得減少。

///|
test "全部套件的 checks() 皆通過且總數不減" {
  let all : Array[Array[(String, Bool, String)]] = [
    @num.checks(),
    @order.checks(),
    @cat.checks(),
    @nbe.checks(),
    @chain.checks(),
    @tm.checks(),
    @path.checks(),
    @trop.checks(),
    @nis.checks(),
    @der.checks(),
    @cat2.checks(),
  ]
  let mut total = 0
  for g in all {
    for (_, ok, _) in g {
      assert_eq(ok, true)
      total = total + 1
    }
  }
  assert_eq(total, 124)
}
