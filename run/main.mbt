///|
fn report(name : String, xs : Array[(String, Bool, String)]) -> Unit {
  println("=== \{name} ===")
  let mut pass = 0
  for t in xs {
    let status = if t.1 { "PASS" } else { "FAIL" }
    if t.1 {
      pass = pass + 1
    }
    println("[\{status}] \{t.0}  —  \{t.2}")
  }
  println("---> \{pass}/\{xs.length()} 通過\n")
}

///|
fn main {
  report("num", @num.checks())
  report("order", @order.checks())
  report("cat", @cat.checks())
  report("nbe", @nbe.checks())
  report("chain", @chain.checks())
  report("tm", @tm.checks())
  report("path", @path.checks())
  report("trop", @trop.checks())
  report("nis", @nis.checks())
  report("der", @der.checks())
  report("cat2", @cat2.checks())
}
