# RatFunc Witt Local-Global

[English](README.md)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22974392.svg)](https://doi.org/10.5281/zenodo.22974392)

このリポジトリは、実閉体 `R` 上の一変数有理関数体 `RatFunc R` に対する、
有限次元二次形式の Witt 型 local-global principle を Lean 4 で形式化します。

## 主定理

有限添字型 `ι` が `3 ≤ Fintype.card ι` を満たすとき、零係数を含む任意の
`a : ι → RatFunc R` に対して次を証明しています。

```lean
#check RatFuncWittLocalGlobal.diagonal_isotropic_iff_not_finiteSameStrictSignOrdering_of_card_ge_three_total
#check RatFuncWittLocalGlobal.diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_same_universe_total
```

第一の定理は、対角形式の isotropy と「全係数が同じ strict sign を持つ ordering が
存在しない」ことを同値にします。第二の定理は、base field 上の isotropy と、
same-universe の全実閉 ordered extension 上の isotropy を同値にします。

Mathlib の一般の有限次元 `QuadraticForm` に対する公開定理もあります。

```lean
#check RatFuncWittLocalGlobal.quadraticForm_not_anisotropic_iff_forall_realClosedExtension_same_universe
```

ここでは isotropy を `¬ Q.Anisotropic` として表すため、退化形式も含まれます。
target universe を変える版は、extension の量化が空虚になることを避けるため、
対応する ordered real closure の存在を明示的な引数として受け取ります。

```lean
#check RatFuncWittLocalGlobal.diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_of_ratFuncClosure
#check RatFuncWittLocalGlobal.diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_of_orderedFieldClosure
#check RatFuncWittLocalGlobal.quadraticForm_not_anisotropic_iff_forall_realClosedExtension_of_ratFuncClosure
#check RatFuncWittLocalGlobal.quadraticForm_not_anisotropic_iff_forall_realClosedExtension_of_orderedFieldClosure
```

次元3以上という条件は本質的です。二次元形式では、同じ主張は一般に成立しません。

## Buildと監査

Lean 4.34.0 と Mathlib v4.34.0 を使用します。

```bash
lake exe cache get
lake build RatFuncWittLocalGlobal
task axiom-audit
task duplicate-declaration-audit
```

数学的な証明本文は英語版と日本語版を用意しています。

- [英語 TeX source](docs/ratfunc_witt_local_global_en.tex)・
  [PDF](docs/ratfunc_witt_local_global_en.pdf)
- [日本語 TeX source](docs/ratfunc_witt_local_global_ja.tex)・
  [PDF](docs/ratfunc_witt_local_global_ja.pdf)

[Task](https://taskfile.dev/) と日本語 TeX 環境があれば、両 PDF を再生成できます。

```bash
task pdf
```

人間向けの証明構造は
[PROOF_ARCHITECTURE.ja.md](PROOF_ARCHITECTURE.ja.md) に記載しています。

公理監査は、対象定理の依存公理が `[propext, Classical.choice, Quot.sound]` と
異なる場合に失敗します。

source scan と style linter は次で実行できます。

```bash
rg -n "^\s*(axiom|unsafe|set_option)\b|\b(sorry|admit)\b" \
  RatFuncWittLocalGlobal RatFuncWittLocalGlobal.lean -S
lake exe lint-style RatFuncWittLocalGlobal
```

利用側では安定した公開入口だけをimportします。

```lean
import RatFuncWittLocalGlobal
```

## 証明経路

```text
ordering obstruction
  -> 非零squarefree polynomial係数
  -> 有限個の実根breakpoint
  -> 必要な符号変化だけを持つsigned linear-root skeleton
  -> 全ordered real-closed imageへのfinite-cut transport
  -> binary head + nonempty tail compression
  -> ternary base caseからの次元帰納
  -> 任意の有限添字型
  -> total diagonal theorem
  -> orthogonal basisによる一般QuadraticFormへの還元
```

三項の基底定理は、ordered real closure の明示的構成と、polynomial
Legendre/quaternion argumentから得ます。一般次元部分は、特殊な四次元定理を
反復するのではなく、符号分離係数による直接的な次元帰納です。

数学的な証明経路は [PROOF_ARCHITECTURE.ja.md](PROOF_ARCHITECTURE.ja.md) に
記載しています。Lean の本線と対応する完全な TeX 証明と保守規約への入口は
[文書案内](docs/README.md) にまとめています。

## Repository layout

- `Core/`: diagonal form、rational function、共通定義。
- `Sign/`: strict sign と有限列上の符号伝播。
- `Polynomial/`: polynomial normal form、root、Laurent局所量、Legendre線形代数。
- `Ordering/`: ordering、ordered algebra extension、ordering obstruction。
- `RealClosure/`: 最大順序付き中間体と ordered real closure の構成。
- `Ternary/`: Legendre/quaternion による三項基底定理。
- `FiniteDimensional/`: compression、次元帰納、公開 endpoints。
- `docs/`: 文書案内と日英の完全なTeX/PDF証明。

ルート module は最終的な二次形式の公開 endpoint を import します。
内部の証明 module は互換性保証の対象に含めません。

## 参考文献

- T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies
  in Mathematics 67, American Mathematical Society, 2005.
- A. Pfister, *Quadratic Forms with Applications to Algebraic Geometry and
  Topology*, London Mathematical Society Lecture Note Series 217, Cambridge
  University Press, 1995.

## ライセンスと引用

著者: **Mocho Go**（[selpoG](https://github.com/selpoG)）。
[ORCID: 0009-0000-8123-9408](https://orcid.org/0009-0000-8123-9408).

ソフトウェアとしての引用情報は [CITATION.cff](CITATION.cff) に記載しています。
引用した形式化を再現できるよう、使用したリリースまたは commit を明記してください。

保存済みの **v0.1.1** は
[10.5281/zenodo.22974393](https://doi.org/10.5281/zenodo.22974393) から参照できます。
冒頭の DOI バッジは、このソフトウェアの全バージョンをまとめたレコードを指します。

[Apache License 2.0](LICENSE) の下で公開しています。
