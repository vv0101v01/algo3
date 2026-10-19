# 超結構 (hyperstructure)：八個數學結構的 MoonBit 實作、演算法與定理驗證

> 目標：把八個抽象數學結構**真正實作出嚟**——唔係型別裝飾、唔係永遠為綠嘅假測試。
> 每一條定理都附上可執行嘅驗證、具體數字，同埋（大部分）**反例見證**，證明個檢查唔係恆真。

- 工具鏈：`moon 0.1.20261012 (748b63c 2026-10-12)`、`moonc v0.10.15+943464bfa`
- 模組：`user/hyperstructure`（`preferred_target = "wasm"`）
- 一句話跑完所有驗證：

```bash
./verify.sh      # 一鍵：檢查 + 測試 + 編譯期證明 + 單態化證據

# 或者逐項：
moon run run      # 11 個套件、124 條檢查，全部真計算，約 0.7 秒
moon test         # 單元測試 + 整合測試（6/6）
moon prove        # 編譯期 SMT 證明（z3）：14 個證明義務全部通過
moon build --target wasm --output-wat   # 產生 WAT，可檢查單態化
```

---

## 0. 成果總覽

| 套件 | 結構 | 檢查數 | 關鍵見證 |
|---|---|---:|---|
| `tm` | 泰希米勒空間 Teichmüller space | 11 | Γ(2) 自由群秩 2（1457 個相異矩陣）、Hasse 界 `max |a_p|/2√p = 0.724` |
| `path` | 路徑空間 path space | 7 | 同倫 ⟺ 既約字相同（116281 對全比對）、`π₁(R_r)=F_r` 計數 `2r(2r−1)^{n−1}` |
| `nis` | 尼雲維奇拓撲 Nisnevich topology | 10 | T1/T2/T3 於 2608 組（覆蓋, 態射）、`Zar ⊊ Nis ⊊ Ét`、subcanonicity |
| `nbe` | 規範形式 normal form (NbE) | 13 | βη-規範、冪等、典範性、η-長 |
| `der` | 導範疇 derived category | 7 | `dim Hom_D(C,D) = Σ h_n h_n`、形式性 `C ≅ H_*(C)`、qis ⟹ 同倫等價 |
| `cat2` | 範疇化 categorification | 9 | `|FinSet_≅| = Σ1/n! = e`（18 位）、Yoneda 窮舉互逆 |
| `trop` | 熱帶化 tropicalization | 8 | Newton 多邊形斜率 = 根賦值、熱帶平衡律 `Σ ℓ·u = 0` |
| `order` | 格及序 lattices & order | 19 | Birkhoff 表示定理、Heyting 伴隨律、Knaster–Tarski |
| `num` | 數論地基（有理數、GF(p)、Legendre） | 7 | Mersenne 縮減、Euler 判準 |
| `chain` | 鏈複形、蛇引理、Ext | 20 | `H_*(S¹)`、Extⁿ、`Z/2 ≅ coker(×2)` |
| `cat` | 有限範疇、預層、Yoneda | 13 | e 的收斂誤差嚴格有理比較 |

合計 **124 條檢查**（全部在 `moon run run` 中真實計算並輸出數據；完整輸出見 [`REPORT.md`](REPORT.md)）。
另有 `proof` 套件：**14 個由 z3 在編譯期證明的引理**（`moon prove`），不執行任何執行期檢查。

---

## 1. 設計原則（回應「唔要玩具模型、唔要假綠」）

1. **每個宣稱都有可執行嘅計算支撐。** 例如 `nis` 唔係「宣告」Zariski ⊆ Nisnevich，
   而係逐個篩（bitmask）比對；`der` 唔係「宣告」導範疇嘅 Hom 維數，而係用精確有理數
   rref 解線性方程組，再同 `Σ h_n h_n` 對照。
2. **每條定理都附非平凡性見證。** 例如：
   - `order`：M3、N5 兩個**非分配格**作為反例（若定理恆真，反例唔會失敗）；
   - `nbe`：`λx.λy.x` 與 `λx.λy.y` **不** βη-相等（區分力見證）；
   - `der`：`cone(f)` 的維數 `[1,3,2,0] ≠ [1,1]`，證明 cone 唔係擺設；
   - `tm`：300 點中 229 點原本不在基本域，歸約後全部入域（若恆真則無需歸約）；
   - `trop`：`val(f+g) = 1 > min(0,0)`，即相消令等號嚴格失效（熱帶化的資訊損失）。
3. **唔用 `assert true`。** 所有檢查都比較兩個獨立計算出嚟嘅結果（例如「矩陣計算」vs「公式計算」）。

---

## 2. 八個結構：定義、公式、定理、驗證

### 2.1 泰希米勒空間 `tm`

**定義.** 上牛平面 $\mathbb H=\{z\in\mathbb C:\operatorname{Im}z>0\}$，雙曲距離

$$
d(z,w)=2\operatorname{artanh}\frac{|z-w|}{|z-\bar w|}
=\operatorname{arcosh}\!\Bigl(1+\frac{|z-w|^2}{2\,\operatorname{Im}z\,\operatorname{Im}w}\Bigr).
$$

同餘子群

$$
\Gamma(2)=\Bigl\{\begin{pmatrix}a&b\\ c&d\end{pmatrix}\in SL_2(\mathbb Z):\ a\equiv d\equiv 1,\ b\equiv c\equiv 0\ (\mathrm{mod}\ 2)\Bigr\}
$$

以 $z\mapsto \frac{az+b}{cz+d}$ 作用。模空間 $T_{0,4}=\mathbb H/\Gamma(2)$，$\dim_{\mathbb C}T_{0,n}=n-3$。
$\lambda$ 函數給出萬有覆蓋 $\lambda:\mathbb H\to\mathbb C\setminus\{0,1\}$，$j$ 不變量

$$
j(\lambda)=2^8\,\frac{(\lambda^2-\lambda+1)^3}{\lambda^2(\lambda-1)^2},
\qquad j(\lambda)=j(1-\lambda)=j(1/\lambda)=j\!\left(\tfrac{\lambda}{\lambda-1}\right).
$$

Legendre 曲線 $E_\lambda:\ y^2=x(x-1)(x-\lambda)$，$\#E(\mathbb F_p)=p+1-a_p$，Hasse：$|a_p|\le 2\sqrt p$。

**實作.** `Cx2`/Möbius 變換、精確 $\Gamma(2)$ 整數矩陣、Euclid 式歸約演算法（把點拉入基本域）、
以 Legendre 符號逐點計數 $\#E(\mathbb F_p)$。

**定理與驗證.**
| 定理 | 驗證方式 | 結果 |
|---|---|---|
| $d(i,2i)=\ln 2$ | 解析值對照 | $0.6931471805599453$ |
| $d$ 在 $\Gamma(2)$ 下不變 | 5 個矩陣、隨機點 | 全部相等（誤差 $<10^{-12}$） |
| 每個點可歸約入基本域 | 300 個隨機點 | 300/300（其中 229 點原本在外） |
| 歸約可逆 | $M^{-1}\cdot\mathrm{reduce}(z)=z$ | 300/300 |
| $\Gamma(2)\cong F_2$（秩 2 自由群） | 長度 $\le 6$ 的既約字 | 1456 個非空字 + 空字 = **1457 個相異矩陣** |
| Hasse 界 | 4 個 $p$ × 4 個 $\lambda$ | $\max |a_p|/2\sqrt p = 0.7241$ |
| 完整 2-撓群 | 16 個樣本 | $4\mid\#E(\mathbb F_p)$ 全成立 |

> 非平凡性：$\lambda=2/3$ 與 $\lambda=3/5$ 的 $j$ 不同（若 $j$ 是常數，這個檢查會失敗）。

### 2.2 路徑空間 `path`

**定義.** 圖 $G$ 的自由群胚 $\Pi_1(G)$：物件為頂點，態射為邊與其形式逆組成的字；
基本關係 $aa^{-1}\to\varepsilon$、$a^{-1}a\to\varepsilon$。既約字 = 無相鄰互逆對。

**定理.**（自由群胚的正規形）每條路徑同倫等價於唯一既約字；因此
$\pi_1(G,v)$ 是自由群，秩 $r=E-V+1$。對玫瑰圖 $R_r$：

$$
\#\{\text{長度 }n\text{ 的既約閉路}\}=2r\,(2r-1)^{n-1}.
$$

**實作.** 堆疊式歸約、複合、反演、DSU（生成樹）、路徑枚舉、同倫類分割。

**驗證.**
- 玫瑰圖 $R_2$、長度 $\le 4$：341 條路徑、**116281 對**全比對，「同倫 ⟺ 既約字相同」成立。
- $\pi_1(R_r)=F_r$：$r=1,2,3$ 時長度 $n$ 的閉路數為 $2,36,150$，與公式 $2r(2r-1)^{n-1}$ 完全一致。
- $\theta$ 圖：閉路數 $3\cdot 2^{n-1}$（$n=2,4$）；91 條閉路兩兩比對，同倫類 $\leftrightarrow$ 非樹邊字。
- 有向路徑（只准前進）：$0\to1$ 的反向步不存在 ⇒ 只係範疇，唔係群胚（$A^1$-同倫 / d-space 的起點）。

### 2.3 尼雲維奇拓撲 `nis`

**定義.** $f:Y\to X$ 在 $x$ 處**完全分解**（cd）：

$$
\exists y\in Y,\ f(y)=x,\quad k(y)\cong k(x)\ \text{（剩餘域同構）}.
$$

一族 $\{f_i:Y_i\to X\}$ 是 Nisnevich 覆蓋 ⟺ 每個 $x$ 處 cd。**定理**（Nisnevich）：

$$
\mathrm{Zar}\ \subseteq\ \mathrm{Nis}\ \subseteq\ \mathrm{\acute Et},\quad\text{兩者嚴格};\qquad \text{Nis 是 subcanonical}.
$$

**有限 Galois 模型.** $G=\mathbb Z/2\times\mathbb Z/2$；有限 étale $X$-概形 $\leftrightarrow$ 有限 $G$-集
（$Y\mapsto Y(\bar x)$）。在此對偶下：

$$
\text{點 }y\text{ 的分解群}=D_y=\operatorname{Stab}_G(y),\qquad
f:Y\to Z\ \text{在 }z\text{ 處 cd}\iff \exists y,\ f(y)=z,\ \operatorname{Stab}(y)=\operatorname{Stab}(z).
$$

於是 cd 條件變成可計算的有限條件；開浸入 = 單射；étale 覆蓋 = 共同滿射。

**驗證（全部窮舉，7 個物件、覆蓋族大小 ≤ 2）**

| 公理 | 規模 | 結果 |
|---|---|---|
| (T1) 極大篩 | 7 個物件 | ✓ |
| (T2) 拉回穩定 | **2608** 組（覆蓋, 態射） | ✓ |
| (T3) 局部性 | **11713** 組複合 | ✓ |
| `Zar ⊆ Nis` | 47 個 Zariski 覆蓋 | ✓ |
| `Nis ⊆ Ét` | 187 個 Nisnevich 覆蓋 | ✓ |
| Subcanonicity | 308 組（覆蓋, $X$) | ✓ |
| 嚴格性 | $\{\mathrm{pt}\sqcup\mathrm{pt}\to\mathrm{pt}\}$（cd 但非單射）；$\{G\to\mathrm{pt}\}$（滿射但無不動點 ⇒ 非 cd） | ✓ |
| 計數 | $|Zar|=47 < |Nis|=187 < |\mathrm{\acute Et}|=318$ | ✓ |

判準（定理）：$\{Y\to\mathrm{pt}\}$ 是 Nisnevich 覆蓋 $\iff$ $Y$ 有 $G$-不動點——對 7 個物件逐一驗證。

### 2.4 規範形式 `nbe`（normalization by evaluation）

**定義.** 簡單型別 λ 演算，$\beta$：$(\lambda x.t)\,u\to t[x:=u]$，$\eta$：$\lambda x.f\,x\to f$（$x\notin fv(f)$）。
NbE 以 `eval : Term → Value` 與 `quote : Value → Term` 給出範式：

$$
\mathrm{nf}(t)=\operatorname{quote}_{\ell}(\operatorname{eval}(t)),\qquad
t=_{\beta\eta}u\iff \mathrm{nf}(t)=\mathrm{nf}(u).
$$

**定理.**（正規化、冪等、典範性、$\eta$-長）
$\mathrm{nf}(\mathrm{nf}(t))=\mathrm{nf}(t)$；閉項 $:\mathrm{Bool}$ 必求值為 `tt` 或 `ff`。

**驗證（13 條）：** 5 個範式樣本全部 β-規範且 η-長；冪等；`(λx.x)(λy.y) =βη λz.z`；
`K = λx.λy.x` 與 `K* = λx.λy.y` **不**相等（區分力）；canonicity；型別保持；
`(λf.λx.f(f x))(λy.y)()` 正規化為 `()`。

### 2.5 導範疇 `der`

**定義.** $\mathrm{Ch}(\mathbb Q)$ 的鏈映射 $f$，同倫 $f\simeq g\iff \exists h,\ f-g=\partial h+h\partial$；

$$
K(\mathbb Q)=\mathrm{Ch}/\simeq,\qquad D^b(\mathbb Q)=K^b(\mathbb Q)[\mathrm{qis}^{-1}].
$$

映射錐：$\mathrm{cone}(f)_n=C_{n-1}\oplus D_n$，$\partial=\begin{pmatrix}-\partial_C&0\\ f&\partial_D\end{pmatrix}$。

**定理.**
1. $f$ 是準同構 $\iff \mathrm{cone}(f)$ 無環。
2. 域上每個複形分裂：$C\cong H_*(C)\oplus(\text{可縮塊})$，故 $D^b(\mathbb Q)\simeq$ 分次向量空間。
3. 推論：$\dim\operatorname{Hom}_D(C,D)=\sum_n h_n(C)\,h_n(D)$。

**驗證（全部用精確有理數線性代數）**

| 定理 | 規模 | 結果 |
|---|---|---|
| (D1) $\mathrm{cone}(f)$ 滿足 $\partial^2=0$ | 24 個隨機鏈映射 | ✓ |
| (D2) 長正合序列 $\dim H_n(\mathrm{cone}\,f)=\dim\operatorname{coker}H_n(f)+\dim\ker H_{n-1}(f)$ | 96 組 $(n,f)$ | ✓ |
| (D3) 同倫不變性 | 64 組 | ✓ |
| (D4) $\dim\operatorname{Hom}_K=$ 鏈映射空間 $-$ 零倫子空間 | 12 對複形 | ✓ |
| (D5) $\dim\operatorname{Hom}_D=\sum h_n h_n$ | 12 對複形 | ✓ |
| (D6) 顯式 $p:C\to H_*(C)$ 為鏈映射兼準同構 | 12 個複形 | ✓ |
| (D7) 準同構 ⟹ 同倫等價（解線性方程造 $g,h,k$） | 10 個準同構 | ✓ |

> 「域上」是必要條件：`chain` 套件另外用 $[\mathbb Z\xrightarrow{2}\mathbb Z]\to\mathbb Z/2$ 展示
> 一個**準同構但非同倫等價**的例子；其關鍵引理 $2a=0\Rightarrow a=0$ 由 `moon prove` 在編譯期證明。

### 2.6 範疇化 `cat2`

**定義.** 範疇化 = 把等式升級為同構。有限集合範疇 $\mathbf{FinSet}$ 範疇化 $\mathbb N$：

$$
\varnothing\leftrightarrow 0,\quad A\sqcup B\leftrightarrow |A|+|B|,\quad A\times B\leftrightarrow |A|\cdot|B|,\quad |\cdot|:\mathbf{FinSet}\to\mathbb N .
$$

群胚基數：$|G|=\sum_x\frac{1}{|\operatorname{Aut}(x)|}$，故

$$
|\mathbf{FinSet}_{\cong}|=\sum_{n\ge 0}\frac{1}{n!}=e .
$$

Yoneda：$\operatorname{Nat}(y(c),F)\cong F(c)$，$y(c)=\operatorname{Hom}_{\mathcal C}(-,c)$。

**驗證.**
- $e$：以 20 項精確有理數計算，$|S_{19}-e|<1/(19!\cdot 10)$，輸出 $2.718281828459045234$（18 位）。
- Yoneda：對 2 個物件、全部 4 個元素窮舉，`Nat(y(c),F)` 與 `F(c)` 的基數相等，且兩個方向互逆。
- 餘積/積的**普遍性質**：窮舉所有 $f,g$，驗證存在唯一 $h$（$\exists!$），不是「有映射就算」。
- 範疇化 ≠ 等式：$A\sqcup B\cong B\sqcup A$ 是同構，但不是恆等（$0\mapsto 4\neq 0$）。
- 解範疇化：$|A\sqcup B|=|A|+|B|$、$|A\times B|=|A||B|$（3,4,2,5 → 7,12,35）。

### 2.7 熱帶化 `trop`

**定義.** 熱帶半環 $(\mathbb R\cup\{\infty\},\oplus=\min,\otimes=+)$。對 Laurent/Puiseux 級數 $f$，$\operatorname{val}(f)$ 為最低次數：

$$
\operatorname{val}(fg)=\operatorname{val}f+\operatorname{val}g,\qquad
\operatorname{val}(f+g)\ \ge\ \min(\operatorname{val}f,\operatorname{val}g),
$$

等號在兩賦值不等時成立；**相消**正是熱帶化的資訊損失。

**定理（Newton–Puiseux / Kapranov 一維情形）.** $f$ 的牛頓多邊形邊的斜率（取負）＝ 根的賦值（含重數）。
**定理（熱帶平衡）.** 對熱帶曲線的每個頂點，$\sum_i \ell_i u_i=0$（$\ell_i$ 為邊權重、$u_i$ 為本原方向）。

**驗證.**
- $\operatorname{val}(fg)=\operatorname{val}f+\operatorname{val}g$：$(3+t^2)(5t^{-1}+7t)$。
- 相消：$f=1-t$、$g=-1+4t^2$ 皆賦值 0，但 $\operatorname{val}(f+g)=1>0$。
- 牛頓多邊形：根 $t,t^{-1},2$ ⇒ 賦值 $(1,-1,0)$；分數情形 $t^{1/2},t^{1/2},t$ ⇒ 斜率 $-1/2$（重數 2）與 $-1$。
- 平衡律：$x^p+y^q+1$ 的牛頓三角形，四個例子皆 $\sum\ell u=0$。
- 熱帶直線 $x+y+1$：三條射線，方向 $(-1,-1),(1,0),(0,1)$，$(-1,-1)+(1,0)+(0,1)=0$。
- min-plus 分配律 64 組；泛型 Horner 應用於熱帶多項式。

### 2.8 格及序 `order`

**定義.** 格 $(L,\vee,\wedge)$；分配格、Heyting 代數（$a\wedge c\le b\iff c\le a\to b$，$a\to b=\bigvee\{c:a\wedge c\le b\}$）。

**定理.**
- **Birkhoff 表示定理**：有限分配格 $L\cong \mathrm{Down}(J(L))$，$J(L)$ 為 join-不可約元。
- **Knaster–Tarski**：單調 $f:L\to L$ 有最小不動點 $\operatorname{lfp}(f)=\bigvee\{x:x\le f(x)\}$。
- Heyting 伴隨律。

**驗證（19 條）**：5 個格（$\mathrm{Div}(30)\cong B_3$、$\mathrm{Div}(12)$、$C_4$、$M_3$、$N_5$）全部格公理；
分配格 vs **M3、N5 反例**（若定理恆真，反例不會失敗）；Birkhoff 對 3 個分配格的同構（$|L|=|Down(J(L))|$、
單射、保 $\vee/\wedge$），並驗證 M3 不滿足前提；Heyting 伴隨律窮舉；$\operatorname{lfp}$ 與 Kleene 迭代一致；
拓撲排序 = 線性擴張。

---

## 3. 「編譯期邏輯 + 零開銷」嘅實際證據

### 3.1 單態化（monomorphization）：trait 泛型 → 直接呼叫

`num.Semiring` 係一個 trait，`horner` 對它泛型。編譯到 wasm 之後，WAT 裡面出現**四個獨立的單態函數**：

```
(func $_M0FP34user14hyperstructure3num6hornerGRP34user14hyperstructure3num2FpE    ...)   ; horner[Fp]
(func $_M0FP34user14hyperstructure3num6hornerGRP34user14hyperstructure3num3RatE   ...)   ; horner[Rat]
(func $_M0FP34user14hyperstructure3num6hornerGRP34user14hyperstructure3num4TropE  ...)   ; horner[Trop]
(func $_M0FP34user14hyperstructure3num6hornerGiE                                  ...)   ; horner[Int]
```

`trop.Trop` 在自己嘅套件實作 `num.Semiring`，一樣被單態化 ⇒ **跨套件抽象都係零開銷**。

整個 `run.wasm`（debug，494 KB）之中：

| 指標 | 數量 |
|---|---:|
| 直接 `call` | 10042 |
| 間接 `call_indirect` | **20**（0.2%，全部來自 stdlib 嘅 `Eq`/`Hash` 動態路徑，類型 `(refany, i32) => i32`） |

即係：本專案嘅數學抽象**冇**引入任何動態分派。

重現方式：

```bash
moon build run --target wasm --output-wat
grep -c call_indirect _build/wasm/debug/build/run/run.wat
grep -oE 'horner[A-Za-z0-9]*' _build/wasm/debug/build/run/run.wat | sort -u
```

### 3.2 編譯期定理證明：`moon prove`（Why3 → z3）

`proof/theorems.mbtp` 有 14 個 `lemma`，全部在**編譯期**由 SMT 求解器證明，唔會在執行期跑：

| 引理 | 陳述 |
|---|---|
| `trop_add_comm` / `trop_add_assoc` / `trop_add_idem` | min 的交換、結合、冪等 |
| `trop_distrib` | $a+\min(b,c)=\min(a+b,a+c)$ |
| `lattice_absorb_join` / `lattice_absorb_meet` | 吸收律 |
| `lattice_distrib` | $\min(a,\max(b,c))=\max(\min(a,b),\min(a,c))$ |
| `int_torsion_free` | $2a=0\Rightarrow a=0$（導範疇反例的核心） |
| `complex_im_in_ker` | $ab=0\Rightarrow a(bx)=0$（$\partial^2=0\Rightarrow \mathrm{im}\subseteq\ker$） |
| `trace_comm` / `det_mul` | $\operatorname{tr}(AB)=\operatorname{tr}(BA)$、$\det(AB)=\det A\det B$（$\Gamma(2)$ 封閉性） |
| `reduce_len` | 自由群消去後長度不增（$0\le n-2k\le n$） |
| `pullback_stab_order` | 拉回時穩定子交集的序骨架 |
| `card_union_comm` | 餘積基數之交換律 |

```
$ moon prove
user/hyperstructure/proof
  Succeeded: 14 goals proved
```

### 3.3 型別層面嘅約束

- 所有核心資料型別都係**不可變 struct + 明確不變量**（例如 `Fp` 的值域 $0\le v<p$、`Rat` 的正分母與 gcd 正規化）。
- `Semiring` trait 只暴露 `zero/one/add/mul`，泛型演算法（Horner）對它抽象，單態化後零成本。
- 驗證程式（`checks()`）與圖書館程式碼分離：圖書館唔含任何 `assert` 或測試邏輯。

### 3.4 測試在 build 階段

`moon test` 會執行 `num` 的單元測試與 `run` 的整合測試；整合測試斷言
「11 個套件、124 條檢查全部通過，且總數不得少於 124」——任何人想刪檢查，測試會失敗。

---

## 4. 專案結構

```
hp/
├── moon.mod                 # user/hyperstructure, preferred_target = "wasm"
├── num/                     # Rat（BigInt 精確有理數）、Fp(Mersenne p=2^31−1)、Legendre、
│                            # Semiring trait、泛型 Horner、單元測試
├── order/                   # 有限格、分配格、Birkhoff、Heyting、Knaster–Tarski
├── cat/                     # 有限範疇、函子、預層、Yoneda、群胚基數 e
├── nbe/                     # STLC + NbE：βη-範式、典範性
├── chain/                   # 矩陣 over ℚ、鏈複形、蛇引理、Ext、Z/2
├── tm/                      # 雙曲距離、Γ(2)、基本域歸約、Legendre 曲線、j 不變量
├── path/                    # 自由群胚、既約字、π₁、θ 圖
├── trop/                    # min-plus、Puiseux 賦值、牛頓多邊形、平衡律
├── nis/                     # 有限 Galois 模型、cd 條件、篩、T1–T3、subcanonicity
├── der/                     # K(ℚ)、cone、Hom_K 線性代數、形式性、qis ⇒ 同倫等價
├── cat2/                    # 有限範疇、Yoneda 窮舉、FinSet、群胚基數 e、普遍性質
├── proof/theorems.mbtp      # 14 個 SMT 引理（moon prove）
├── tests/all_test.mbt       # 整合測試：124 條檢查必須全部通過
├── run/                     # 可執行檔：印出所有套件的檢查結果
└── verify.sh                # 一鍵驗證腳本
```

---

## 5. 已知限制（誠實聲明）

1. **`tm`**：雙曲幾何用 `Double`（浮點），誤差以 $10^{-12}$ 為界；$\#E(\mathbb F_p)$ 以暴力逐點計數（$p<1000$），
   不是 Schoof 演算法。$\lambda$ 只作為 $T_{0,4}$ 的座標，未實作一般 $T_{g,n}$ 的 Fenchel–Nielsen 座標。
2. **`nis`**：驗證的是**有限模型**（7 個物件、覆蓋族大小 ≤ 2、$G=\mathbb Z/2\times\mathbb Z/2$），
   不是一般概形的 Nisnevich 拓撲。模型精確捕捉了 cd 條件與 subcanonicity，但「有限片段」唔等於全範疇。
3. **`der`**：域 $\mathbb Q$ 上的複形（此時每個準同構都是同倫等價）；$\mathbb Z$ 上的反例以結構方式驗證
   （配以編譯期引理 $2a=0\Rightarrow a=0$），未實作完整 Smith 正規形。
4. **`proof`**：14 個引理是關鍵步驟的機器證明，不是整個理論的形式化。
5. **`path`**：同倫等價以「既約字相同」判定（自由群胚情形），不涉及高維同倫。

---

## 6. 附錄：核心公式一覽

$$
\begin{aligned}
& d(z,w)=2\operatorname{artanh}\frac{|z-w|}{|z-\bar w|}, \qquad
  T_{0,n}=\mathbb H/\Gamma(2),\ \dim_{\mathbb C}T_{0,n}=n-3,\\
& j(\lambda)=2^8\frac{(\lambda^2-\lambda+1)^3}{\lambda^2(\lambda-1)^2},\qquad
  \#E_\lambda(\mathbb F_p)=p+1-a_p,\ |a_p|\le 2\sqrt p,\\
& \#\{\text{長度 }n\text{ 既約閉路}\}=2r(2r-1)^{n-1},\qquad \pi_1(G)=F_{\,E-V+1},\\
& f\ \text{cd at }x\iff \exists y,\ k(y)\cong k(x);\qquad
  \mathrm{Zar}\subseteq\mathrm{Nis}\subseteq\mathrm{\acute Et},\\
& \mathrm{nf}=\operatorname{quote}\circ\operatorname{eval},\quad
  t=_{\beta\eta}u\iff \mathrm{nf}(t)=\mathrm{nf}(u),\\
& \mathrm{cone}(f)_n=C_{n-1}\oplus D_n,\quad
  \dim\operatorname{Hom}_D(C,D)=\sum_n h_n(C)h_n(D),\\
& |\mathbf{FinSet}_\cong|=\sum_{n\ge0}\frac{1}{n!}=e,\qquad
  \operatorname{Nat}(y(c),F)\cong F(c),\\
& \operatorname{val}(fg)=\operatorname{val}f+\operatorname{val}g,\quad
  \operatorname{val}(f+g)\ge\min(\operatorname{val}f,\operatorname{val}g),\quad
  \textstyle\sum_i \ell_i u_i=0,\\
& a\wedge c\le b\iff c\le a\to b,\qquad
  L\cong\mathrm{Down}(J(L)),\qquad
  \operatorname{lfp}(f)=\bigvee\{x:x\le f(x)\}.
\end{aligned}
$$
