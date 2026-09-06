# 保守ガイド

この文書は、公開リポジトリを変更する際の最小限の運用規約です。利用方法は
`README.md` / `README.ja.md`、証明構造は `PROOF_ARCHITECTURE.md` /
`PROOF_ARCHITECTURE.ja.md`、完全な数学的証明は `docs/` の TeX/PDF を正本とします。

## 対応範囲

保守対象は、実閉体 `R` 上の `RatFunc R` における、次元 3 以上の有限次元二次形式の
local-global principle です。

- 対角形式には零係数を含む total API があります。
- 一般の有限次元 `QuadraticForm` に対する公開 wrapper があります。
- 無条件の real-closed-extension endpoint は same-universe です。
- 異なる universe では、ordered real-closed extension の構成データを明示的に渡します。

## Source と module

- 利用者向けの入口は `import RatFuncWittLocalGlobal` の一つです。
- 新しい宣言は、それを最初に必要とする最小の責務別 module に置きます。
- 下位層から `Ternary` や `FiniteDimensional` などの上位層を import しません。
- module の基本方向は
  `Core -> Sign/Ordering -> Polynomial -> RealClosure/Ternary -> FiniteDimensional`
  です。
- 大きなファイルは行数だけでなく責務で分割し、定義・基本補題・主要 consumer の
  まとまりを保ちます。
- 公開 endpoint に到達しない探索的証明は main branch に追加しません。

## Universe 方針

target universe を無条件に変えると、対象 extension が存在せず量化が空虚になる場合が
あります。cross-universe theorem は、適切な ordered real-closed extension を入力として
受け取る現在の API 形状を維持してください。

## 検証手順

Lean toolchain は Lean 4.33.0、Mathlib は v4.33.0 に固定します。commit 前には
少なくとも次を実行します。

```bash
lake build RatFuncWittLocalGlobal
lake exe lint-style RatFuncWittLocalGlobal
task axiom-audit
task duplicate-declaration-audit
rg -n "^\s*(axiom|unsafe|set_option)\b|\b(sorry|admit)\b" \
  RatFuncWittLocalGlobal RatFuncWittLocalGlobal.lean -S
git diff --check
```

数学的説明を変更した場合は、日英の TeX と proof architecture を同時に見直し、
次で PDF を再生成します。

```bash
task pdf
```

`task pdf` は日英 PDF の生成後、TeX log に warning、overfull box、未解決参照、
error がないことを検査します。日本語 PDF の bookmark と metadata には `pxjahyper` を
使用し、文字化けがないことも確認します。

## Release checklist

- root build と style lint が warning なしで成功する。
- README の公開 API と実際の theorem signature が一致する。
- TeX/PDF が Lean の証明本線と同じ補題・帰納・場合分けを記述する。
- Markdown の相対 link と生成済み PDF が有効である。
- placeholder、独自公理、`unsafe`、局所的な `set_option` がない。
- `git diff --check` が成功し、意図しない生成物がない。
