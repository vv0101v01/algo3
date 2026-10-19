# 驗證報告 (REPORT)

以下為 `./verify.sh` 嘅實際輸出（本機執行，非人手編輯）。

```
$ moon run run
=== num ===
[PASS] Fp::mul 與 BigInt 參照一致（Mersenne 縮減）  —  7 個含邊界樣本
[PASS] GF(2^31-1) 域公理（結合/分配/反元素）  —  200 組隨機樣本
[PASS] Legendre/Euler 判準 + sqrt 互逆  —  i < 2000
[PASS] 二次剩餘密度 = 1/2（前 2000 個元素）  —  χ=1 的個數 = 1016
[PASS] Rat 正規化（gcd、正分母）與體運算  —  2/3 + 3/4 = 17/12
[PASS] 泛型 Horner 於 Int/Fp/Rat 單態化後皆正確  —  321, 321, 3
[PASS] 非平凡性：(p-1)^2 mod p = 1（需要兩次縮減）  —  (p-1)^2 = p^2-2p+1
---> 7/7 通過

=== order ===
[PASS] 格公理：Div(30) (≅B3)  —  8 元素
[PASS] 格公理：Div(12)  —  6 元素
[PASS] 格公理：C4  —  4 元素
[PASS] 格公理：M3  —  5 元素
[PASS] 格公理：N5  —  5 元素
[PASS] 分配律：Div(30)  —  布林格必分配
[PASS] 分配律：Div(12)  —  除數格分配
[PASS] 非分配證人：M3  —  M3 違反分配律
[PASS] 非分配證人：N5  —  N5 違反分配律
[PASS] Birkhoff：Div(30) ≅ Down(J)  —  |J(L)|=3, |L|=8, |Down(J(L))|=8, 單射=true, 保 join/meet=true
[PASS] Birkhoff：Div(12) ≅ Down(J)  —  |J(L)|=3, |L|=6, |Down(J(L))|=6, 單射=true, 保 join/meet=true
[PASS] Birkhoff：C4 ≅ Down(J)  —  |J(L)|=3, |L|=4, |Down(J(L))|=4, 單射=true, 保 join/meet=true
[PASS] 非平凡性：M3 不滿足 Birkhoff 前提（非分配）  —  |J(L)|=3, |L|=5, |Down(J(L))|=8, 單射=true, 保 join/meet=false
[PASS] Heyting 伴隨律：Div(30)  —  a∧c ≤ b ⟺ c ≤ a→b
[PASS] Heyting 伴隨律：Div(12)  —  a∧c ≤ b ⟺ c ≤ a→b
[PASS] Heyting 偽：a → ⊥ ≠ ⊥（非布林格）  —  6 個元素
[PASS] Knaster–Tarski：最小不動點存在且最小  —  x ↦ x∨2
[PASS] Knaster–Tarski：恆等映射的 lfp = ⊥  —  
[PASS] 拓撲排序 = 線性擴張  —  C4 上唯一
---> 19/19 通過

=== cat ===
[PASS] 範疇公理：走路箭頭 1→0  —  3 態射
[PASS] 範疇公理：群 C2  —  2 態射
[PASS] 範疇公理：群 C3  —  3 態射
[PASS] 範疇公理：偏序範疇 C3  —  6 態射
[PASS] 函子律：id_C2  —  
[PASS] 非函子證人：把單位映到非單位  —  
[PASS] 預層律：常數預層（走路箭頭上）  —  
[PASS] 可表預層 y(0) 是預層  —  
[PASS] Yoneda 引理：Nat(y(c),F) ≅ F(c)（雙向窮舉）  —  枚舉了 4 個自然變換
[PASS] Yoneda：Nat(y(0), y(1)) ≅ y(1)(0) = Hom(0,1)  —  1 個元素（就是 f）
[PASS] 有限集合群胚基數 Σ1/n! (n≤15) 逼近 e（前 12 位）  —  2.7182818284590452
[PASS] 收斂誤差 < 1/(N!·N) + 1e-16（有理數嚴格比較）  —  N=18
[PASS] 非平凡性：S_N 嚴格遞增（尾項 1/N! > 0）  —  
---> 13/13 通過

=== nbe ===
[PASS] (λx.x)(λy.y) ⇒ λx.x  —  λ.(x0)
[PASS] (λx.λy.x)() ⇒ λy.()  —  λ.(())
[PASS] π₁⟨(),λx.x⟩ ⇒ ()  —  ()
[PASS] if tt then () else () ⇒ ()  —  ()
[PASS] η：λx.(λy.y)x ≡ λx.x  —  λ.(x0)
[PASS] 所有正規形式皆 β-規範且 η-長  —  5 個樣本
[PASS] 冪等：normalize ∘ normalize = normalize  —  
[PASS] βη-相等但語法不同：(λx.x)(λy.y) vs λz.z  —  
[PASS] 非平凡性：λx.λy.x 與 λx.λy.y 不 βη-相等  —  K ≠ K*
[PASS] 典範性 (canonicity)：Bool 閉項 ⇒ tt 或 ff  —  3 個樣本
[PASS] 型別保持：normalize(e) 與 e 同型  —  
[PASS] 型別檢查器拒絕 (λx:2.x) tt？— 應接受；拒絕 App((),())  —  ill-typed 被拒
[PASS] (λf.λx.f(f x))(λy.y)() ⇒ ()  —  ()
---> 13/13 通過

=== chain ===
[PASS] S¹ 鏈複形：∂² = 0  —  3 頂點 3 邊
[PASS] H_*(S¹) = (1,1)  —  H_0=1, H_1=1
[PASS] Euler–Poincaré：χ(S¹) = Σ(-1)^i dim H_i  —  χ = 0 = 3 - 3
[PASS] S² 鏈複形：∂² = 0  —  4 頂點 6 邊 4 面
[PASS] H_*(S²) = (1,0,1)  —  H_0=1, H_1=0, H_2=1
[PASS] Euler–Poincaré：χ(S²) = 2  —  χ = 4 - 6 + 4 = 2
[PASS] 非平凡性：實心三角形 H_1 = 0（收縮）  —  H_0=1, H_1=0
[PASS] C 無環 (H=0,0)  —  0→Q→Q→0
[PASS] D 無環 (H=0,0,0)  —  0→Q→Q²→Q→0
[PASS] C → D 是鏈映射（∂f = f∂）  —  含非平凡矩陣
[PASS] cone(f)：∂² = 0  —  維數 [1, 3, 2, 0]
[PASS] 準同構 ⇒ cone(f) 無環  —  H=[0, 0, 0, 0]
[PASS] cone(id) 無環  —  
[PASS] 非平凡性：cone 的維數 ≠ C 或 D 的維數（非擺設）  —  [1, 3, 2, 0] vs [1, 1]
[PASS] 蛇引理：200 個隨機精確圖，六個位置全部正合  —  200/200 通過
[PASS] 非平凡性：其中 199 例的 a,c 非零（非退化圖）  —  
[PASS] k[x]/x²：ker(×x) = im(×x) = (x)（窮舉 4 元素）  —  
[PASS] Ext^n_{k[x]/x²}(k,k) = k（n=0..4，每個維度 1）  —  ≅ k[t]
[PASS] Z/2Z ≅ coker(×2)：商映射在 |n|≤50 上核 = im  —  H_0(C) = Z/2
[PASS] 非平凡性：Z/2 → Z 的同態必為 0（moon prove 另證 2a=0 ⟹ a=0）  —  故此準同構無同倫逆 ⇒ 導範疇中同構而在 K(Z) 中不同構
---> 20/20 通過

=== tm ===
[PASS] d(i, 2i) = ln 2  —  0.6931471805599453
[PASS] 雙曲距離在 Γ(2) 下不變（5 個矩陣）  —  d = 1.418384983559538
[PASS] Γ(2) 歸約：300 點全部落入基本域且矩陣 ∈ Γ(2)  —  
[PASS] 非平凡性：其中 229 個起點原本不在基本域內  —  
[PASS] 歸約可逆：M⁻¹·reduce(z) 還原 z  —  一致性檢查
[PASS] Γ(2) 自由群秩 2：長度 1..6 的 1456 個既約字全給出相異矩陣  —  非空既約字 4(3⁰+…+3⁵) = 1456，加空字共 1457
[PASS] Legendre 曲線：|#E − (p+1)| ≤ 2√p（4 個 p × 4 個 λ）  —  max |a_p|/2√p = 0.7240728325236424
[PASS] 完整 2-撓群 ⇒ 4 | #E(F_p)  —  16 個樣本
[PASS] j(λ) = j(1/λ) = j(1−λ) = j(λ/(λ−1))（精確有理數）  —  5 個 λ
[PASS] 非平凡性：λ=2/3 與 λ=3/5 的 j 不同  —  
[PASS] dim T_{0,4} = 4 − 3 = 1（複維數）  —  dim_C T_{0,n} = n − 3
---> 11/11 通過

=== path ===
[PASS] 同倫類 ⟺ 既約形式相同（玫瑰圖 R2，長度 ≤4，116281 對）  —  341 條路徑
[PASS] 自由群胚公理：結合律、單位、反元素  —  p1p2p3 兩種括號
[PASS] π₁(玫瑰圖) = F_r：長度 n 既約閉路數 = 2r(2r−1)^{n−1}  —  r=1: 2 (期望 2)；r=2: 36 (期望 36)；r=3: 150 (期望 150)；
[PASS] 有向路徑空間：0→1 的反向步不可容許（範疇而非群胚）  —  反向邊不存在 ⇒ 非群胚，這是 A¹-同倫與 d-space 的起點
[PASS] θ 圖既約閉路計數 = 3·2^{n−1}（n=2,4）  —  r = E − V + 1 = 2
[PASS] π₁(θ) ≅ F₂：同倫類 ⟺ 非樹邊字相同（91 條閉路兩兩比較）  —  生成樹邊被消去，兩條非樹邊給出自由生成元
[PASS] F₂ 既約字增長 4·3^{n−1}  —  n=1: 4 n=2: 12 n=3: 36 
---> 7/7 通過

=== trop ===
[PASS] val(f·g) = val f + val g  —  3·t^0 + 1·t^2 × 5·t^-1 + 7·t^1
[PASS] 相消：val(f+g) > min(val f, val g)（熱帶化的資訊損失）  —  f = 1−t（val 0）、g = −1+4t²（val 0），但 val(f+g) = 1 > 0
[PASS] Newton–Puiseux：根的賦值 = −(多邊形邊斜率)  —  根 t, t⁻¹, 2 ⇒ 賦值 (1, −1, 0)
[PASS] 分數賦值：根 t^{1/2}, t^{1/2}, t ⇒ 斜率 −1/2（重數 2）與 −1  —  (1, ×1) (1/2, ×2) 
[PASS] 熱帶平衡律 Σ ℓ·u = 0（x^p+y^q+1 的牛頓三角形）  —  (1,1)→(0,0) (2,3)→(0,0) (3,5)→(0,0) (4,6)→(0,0) 
[PASS] 熱帶曲線 = corner locus（x+y+1 的熱帶直線）  —  3 條射線
[PASS] min-plus 半環分配律（64 組）  —  a⊗(b⊕c) = (a⊗b)⊕(a⊗c)
[PASS] 泛型 Horner 用於熱帶多項式  —  min(0, 3+2, 1+4) = 0
---> 8/8 通過

=== nis ===
[PASS] (T1) 極大篩 {id_Y} 為 Nisnevich 覆蓋  —  7 個物件
[PASS] (T2) 拉回穩定：f*(cd 覆蓋) 仍為 cd 覆蓋  —  2608 組 (覆蓋, 態射)
[PASS] (T3) 局部性：覆蓋的覆蓋仍為覆蓋  —  11713 組複合
[PASS] Zariski ⊆ Nisnevich（單射族必 cd）  —  47 個 Zariski 覆蓋
[PASS] Nisnevich ⊆ étale（cd ⇒ 共同滿射）  —  187 個 Nisnevich 覆蓋
[PASS] 嚴格性 Nisnevich ⊋ Zariski：{pt ⊔ pt → pt}  —  cd 但非單射（非開浸入）
[PASS] 嚴格性 étale ⊋ Nisnevich：{G → pt}（自由軌道）  —  滿射但無 G-不動點 ⇒ 非 cd
[PASS] 判準：{Y → pt} 是 Nisnevich 覆蓋 ⟺ Y 有 G-不動點  —  7 個物件
[PASS] Subcanonicity：可表預層 h_X 對 Nisnevich 覆蓋是層  —  308 組 (覆蓋, X)
[PASS] 覆蓋計數：|Zar| ≤ |Nis| ≤ |Ét|  —  Zar = 47，Nis = 187，ét = 318
---> 10/10 通過

=== der ===
[PASS] (D1) 映射錐 cone(f) 滿足 ∂² = 0  —  24 個隨機鏈映射
[PASS] (D2) 長正合序列：dim H_n(cone f) = dim coker H_n(f) + dim ker H_{n−1}(f)  —  96 個 (n, f) 組合
[PASS] (D3) 同倫不變性：f ≃ g ⟹ H_n(f) = H_n(g)  —  64 個 (n, 配對)
[PASS] (D4) Hom_K = 鏈映射空間 / 零倫子空間（精確 rref 維度）  —  12 對複形
[PASS] (D5) dim Hom_D(C,D) = Σ_n h_n(C)·h_n(D)（形式性推論）  —  12 對複形
[PASS] (D6) 形式性：顯式 p : C → H_*(C) 為鏈映射且誘導同構  —  12 個隨機複形
[PASS] (D7) 準同構 ⟹ 同倫等價：解線性方程構造 (g, h, k)  —  10 個準同構
---> 7/7 通過

=== cat2 ===
[PASS] 範疇公理（走路箭頭、C₃、3 元鏈偏序）  —  3 個範疇、結合律與單位律窮舉
[PASS] 函子律（保單位、保合成）+ 非函子見證  —  2 個函子、1 個反例
[PASS] 天然變換的自然性方形 + 非天然見證  —  1 個天然、1 個非天然
[PASS] Yoneda：Nat(y(c), psh) ≅ psh(c)（雙向互逆 + 基數相等）  —  4 個元素、2 個物件窮舉
[PASS] 群胚基數 |FinSet_≅| = Σ 1/n! = e（20 項，誤差 < 1/(19!·10)）  —  2.718281828459045234
[PASS] 解範疇化 |A ⊔ B| = |A|+|B|、|A × B| = |A|·|B|  —  基數 3,4,2,5 → 7,12,35
[PASS] 餘積普遍性質：∃! h : A ⊔ B → C（窮舉所有 f, g, h）  —  大小 (2,2,2)、(2,3,2)
[PASS] 積普遍性質：∃! h : C → A × B（窮舉所有 f, g, h）  —  大小 (2,2,2)、(2,3,2)
[PASS] 範疇化把等式換成同構：A ⊔ B ≅ B ⊔ A（非恆等）  —  雙射存在但 0 ↦ 4 ≠ 0
---> 9/9 通過


$ moon test
Total tests: 6, passed: 6, failed: 0.

$ moon prove
user/hyperstructure/proof
  Succeeded: 14 goals proved

Summary:
  1 of 1 packages proved
  14 goals proved
```
