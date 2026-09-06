# 文書案内

| 読みたい内容 | 文書 |
| --- | --- |
| 概要・公開 API・build 方法 | [README (English)](../README.md) / [README (日本語)](../README.ja.md) |
| 人間向けの証明構造 | [Proof architecture (English)](../PROOF_ARCHITECTURE.md) / [証明構造 (日本語)](../PROOF_ARCHITECTURE.ja.md) |
| Lean 本線と対応する完全な数学的証明 | [English PDF](ratfunc_witt_local_global_en.pdf) / [日本語 PDF](ratfunc_witt_local_global_ja.pdf) |
| TeX source | [English](ratfunc_witt_local_global_en.tex) / [日本語](ratfunc_witt_local_global_ja.tex) |
| 保守・検証・release 規約 | [保守ガイド](../MAINTENANCE.md) |

## 数学的証明

日英の文書は、ordering、quaternion symbol、Laurent ordering、polynomial pivot を用いた
証明と、数学的補題に対応する Lean 宣言を掲載しています。

PDF は次で再生成します。

```bash
task pdf
```
