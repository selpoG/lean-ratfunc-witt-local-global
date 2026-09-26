# RatFunc Witt Local-Global

[日本語版](README.ja.md)

This repository formalizes in Lean 4 a Witt-type local-global principle for
finite-dimensional quadratic forms over the rational function field
`RatFunc R`, where `R` is real closed.

## Main theorems

For a finite index type `ι` with at least three elements and any diagonal
coefficient family `a : ι → RatFunc R`, including families with zero
coefficients, the library proves:

```lean
#check RatFuncWittLocalGlobal.diagonal_isotropic_iff_not_finiteSameStrictSignOrdering_of_card_ge_three_total
#check RatFuncWittLocalGlobal.diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_same_universe_total
```

The first theorem characterizes isotropy by the absence of an ordering at
which all coefficients have the same strict sign. The second characterizes
isotropy over `RatFunc R` by isotropy after scalar extension to every real
closed ordered extension in the same universe.

The result is also exposed for Mathlib's general finite-dimensional
`QuadraticForm` API. The statement uses `¬ Q.Anisotropic`, so degenerate and
isotropic forms are handled without a regularity assumption:

```lean
#check RatFuncWittLocalGlobal.quadraticForm_not_anisotropic_iff_forall_realClosedExtension_same_universe
```

Universe-parameterized variants take an explicit ordered-real-closure input,
preventing the quantified class of target extensions from becoming vacuous:

```lean
#check RatFuncWittLocalGlobal.diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_of_ratFuncClosure
#check RatFuncWittLocalGlobal.diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_of_orderedFieldClosure
#check RatFuncWittLocalGlobal.quadraticForm_not_anisotropic_iff_forall_realClosedExtension_of_ratFuncClosure
#check RatFuncWittLocalGlobal.quadraticForm_not_anisotropic_iff_forall_realClosedExtension_of_orderedFieldClosure
```

Dimension at least three is essential. Binary forms over a rational function
field do not satisfy the same statement in general.

## Build and verification

The project uses Lean 4.34.0 and Mathlib v4.34.0 through Lake.

```bash
lake exe cache get
lake build RatFuncWittLocalGlobal
```

The mathematical proof is available in both English and Japanese:

- [English TeX source](docs/ratfunc_witt_local_global_en.tex) and
  [compiled PDF](docs/ratfunc_witt_local_global_en.pdf)
- [Japanese TeX source](docs/ratfunc_witt_local_global_ja.tex) and
  [compiled PDF](docs/ratfunc_witt_local_global_ja.pdf)

With [Task](https://taskfile.dev/) and a Japanese TeX installation, rebuild
both PDFs with:

```bash
task pdf
```

The human proof route is described in
[PROOF_ARCHITECTURE.md](PROOF_ARCHITECTURE.md). Reproducible axiom and normalized
duplicate-declaration audits are available with:

```bash
task axiom-audit
task duplicate-declaration-audit
```

The axiom audit fails if the checked theorems' dependencies differ from
`[propext, Classical.choice, Quot.sound]`.

For a source scan and Mathlib's text-based style linter, run:

```bash
rg -n "^\s*(axiom|unsafe|set_option)\b|\b(sorry|admit)\b" \
  RatFuncWittLocalGlobal RatFuncWittLocalGlobal.lean -S
lake exe lint-style RatFuncWittLocalGlobal
```

Users should import only the stable public entry point:

```lean
import RatFuncWittLocalGlobal
```

## Proof strategy

The maintained proof spine is:

```text
ordering obstruction
  -> nonzero squarefree polynomial coefficients
  -> finitely many real-root breakpoints
  -> signed linear-root skeleton with exactly the required sign changes
  -> finite-cut transport to every ordered real-closed image
  -> binary-head/nonempty-tail compression
  -> dimension induction from the ternary base case
  -> arbitrary finite index types
  -> total diagonal theorem
  -> orthogonal-basis reduction for general quadratic forms
```

The ternary base case is obtained from an explicitly constructed ordered real
closure and a polynomial Legendre/quaternion argument. The general-dimensional
proof then uses a direct sign-separating compression coefficient; it does not
iterate special rank-four arguments.

See [PROOF_ARCHITECTURE.md](PROOF_ARCHITECTURE.md) for the mathematical proof
route. The [documentation guide](docs/README.md) links the complete TeX proof, the
proof architecture, and the maintainer policy without duplicating them here.

## Repository layout

- `RatFuncWittLocalGlobal/Core`: diagonal forms, rational functions, and common definitions.
- `RatFuncWittLocalGlobal/Sign`: strict-sign data and finite sign propagation.
- `RatFuncWittLocalGlobal/Polynomial`: polynomial normal forms, roots, Laurent data,
  ordered-image sign transport, and Legendre linear algebra.
- `RatFuncWittLocalGlobal/Ordering`: orderings, ordered algebra extensions, and obstructions.
- `RatFuncWittLocalGlobal/RealClosure`: maximal ordered intermediate fields and the
  construction of an ordered real closure.
- `RatFuncWittLocalGlobal/Ternary`: the Legendre/quaternion ternary base case.
- `RatFuncWittLocalGlobal/FiniteDimensional`: compression, dimension induction, and
  the public diagonal and quadratic-form endpoints.
- `docs/`: documentation index and the complete English/Japanese TeX/PDF proofs.

The root module imports only the final public quadratic-form endpoint. Internal
proof modules are not part of the compatibility promise.

## References

- T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies
  in Mathematics 67, American Mathematical Society, 2005.
- A. Pfister, *Quadratic Forms with Applications to Algebraic Geometry and
  Topology*, London Mathematical Society Lecture Note Series 217, Cambridge
  University Press, 1995.

## License and citation

Author: **Mocho Go** ([selpoG](https://github.com/selpoG)).
[ORCID: 0009-0000-8123-9408](https://orcid.org/0009-0000-8123-9408).

Please cite the software using [CITATION.cff](CITATION.cff), and identify the
release or commit you used so that the cited formalization is reproducible.

Released under the [Apache License 2.0](LICENSE).
