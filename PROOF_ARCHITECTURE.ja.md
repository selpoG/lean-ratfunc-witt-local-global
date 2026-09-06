# 証明アーキテクチャ

[English](PROOF_ARCHITECTURE.md)

この文書は `lean-ratfunc-witt-local-global` の証明方針と module の依存関係を説明します。

Lean の本線と対応する完全な数学的証明、および Lean 宣言との対応表は、
[日本語版](docs/ratfunc_witt_local_global_ja.pdf)・
[英語版](docs/ratfunc_witt_local_global_en.pdf)にまとめています。

## 公開境界

主要な対角形式定理は次です。

```lean
RatFuncWittLocalGlobal.diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_same_universe_total
```

実閉体 `R`、`3 ≤ Fintype.card ι` を満たす有限型 `ι`、および
`a : ι → RatFunc R` に対し、base field 上の isotropy と same-universe の
全実閉 ordered extension 上の isotropy を同値にします。零係数は定理内部で処理します。

座標に依存しない一般二次形式版は次です。

```lean
RatFuncWittLocalGlobal.quadraticForm_not_anisotropic_iff_forall_realClosedExtension_same_universe
```

この定理は `3 ≤ Module.finrank (RatFunc R) V` を満たす任意の有限次元空間上の
`QuadraticForm (RatFunc R) V` に適用できます。

## 証明の依存鎖

```text
ordered real closure + polynomial Legendre/quaternion argument
  -> ternary local-global theorem

squarefree polynomial normalization
  + signed linear-root skeleton
  + ordered-image finite-cut transport
  -> binary-tail compression coefficient
  -> 一次元ずつ進む次元帰納
  -> finite-dimensional diagonal theorem
  -> orthogonal-basis reduction
  -> general quadratic-form theorem
```

一般次元の帰納は四次元定理を仮定しません。三項定理を基底とし、係数族を
binary head と nonempty tail に分ける successor step だけで進みます。

## 三項基底

三項層は次の二つから構成されます。

1. `RealClosure/` で最大順序付き中間体を構成し、非負元の平方根拡大と
   奇数次既約因子の根拡大を最大性で排除して実閉性を示す。
2. `Ternary/` で三項対角形式を quaternion symbol へ移し、polynomial
   Legendre criterion を閉じる。

この層から一般次元へ出る公開bridgeは `Ternary.NormalizedLocalGlobal` です。
`FiniteDimensional/` は quaternion residue の内部実装を直接importしません。

## Binary-tail compression

零係数の場合を処理した後、元の係数族には全係数が同じ狭義符号を持つ ordering がないとします。
binary head `a₀, a₁` と非空tail `ψ` に対し、全orderingで

```text
<a₀, a₁, c>
<ψ, -c>
```

の双方が definite にならないような非零有理関数 `c` を一つ構成します。

1. 平方因子を除去し、非零squarefree polynomial係数へ正規化する。
2. 全係数の実根を有限個のbreakpointとして集める。
3. 各補区間で必要な `c` の符号を決める。
4. 必要符号が変化するbreakpointだけを単純根に持つlinear-factor積を作る。
5. ordinary real point上の計算をfinite cutにより全ordered real-closed imageへ輸送する。
6. headには三項定理、augmented tailには帰納仮定を適用し、元のisotropic vectorを再構成する。

停止性は次元そのものであり、`Fin n` 上の結果を `Fintype.equivFin` で任意有限型へ戻します。

## 一般二次形式

Mathlib のorthogonal basisにより、一般の有限次元二次形式をweighted sum of squaresへ
移します。total diagonal theoremを適用し、isometryとscalar extensionを通して
anisotropyを輸送します。

## Module階層

依存方向は次の一方向に保ちます。

```text
Core -> Sign/Ordering -> Polynomial -> RealClosure/Ternary -> FiniteDimensional
```

- `Core/`: 対角形式と有理関数の基礎。
- `Sign/`: 表示に依存しない狭義符号のデータ。
- `Ordering/`: ordering と同一狭義符号による障害。
- `Polynomial/`: 多項式、Laurent 級数、有限 cut、Legendre の線形代数。
- `RealClosure/`: 三項基底で使う順序付き実閉包。
- `Ternary/`: 三項局所大域定理。
- `FiniteDimensional/`: 圧縮、次元帰納、公開定理。

Legendre・quaternion の長い証明は責務別submoduleへ分割済みです。
三項 reduction の命題定義は `Ternary/Reduction/Basic.lean`、多項式正規化は
`Ternary/Reduction/PolynomialNormalization.lean` に分離しています。

## 関連文書

- 完全な数学的証明は [TeX](docs/ratfunc_witt_local_global_ja.tex) と
  [PDF](docs/ratfunc_witt_local_global_ja.pdf) にあります。
- build、公理監査、release、研究archiveの規約は
  [保守ガイド](MAINTENANCE.md) にあります。
- 全文書の入口は [文書案内](docs/README.md) です。
