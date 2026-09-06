# Proof Architecture

[日本語版](PROOF_ARCHITECTURE.ja.md)

This note describes the proof strategy and module dependencies of
`lean-ratfunc-witt-local-global`.

A complete mathematical proof, including a table relating its lemmas to Lean
declarations, is available in [English](docs/ratfunc_witt_local_global_en.pdf)
and [Japanese](docs/ratfunc_witt_local_global_ja.pdf).

## Public boundary

The primary diagonal theorem is:

```lean
RatFuncWittLocalGlobal.diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_same_universe_total
```

For a real closed field `R`, a finite type `ι` with `3 ≤ Fintype.card ι`, and
`a : ι → RatFunc R`, it states that the diagonal form with coefficients `a` is
isotropic over `RatFunc R` exactly when it is isotropic over every same-universe
real closed ordered extension. Zero coefficients are handled internally.

The coordinate-free endpoint is:

```lean
RatFuncWittLocalGlobal.quadraticForm_not_anisotropic_iff_forall_realClosedExtension_same_universe
```

It applies to any finite-dimensional `QuadraticForm (RatFunc R) V` with
`3 ≤ Module.finrank (RatFunc R) V`.

## Dependency spine

```text
ordered real closure + polynomial Legendre/quaternion argument
  -> ternary local-global theorem

squarefree polynomial normalization
  + signed linear-root skeleton
  + ordered-image finite-cut transport
  -> binary-tail compression coefficient
  -> one-dimensional induction step
  -> finite-dimensional diagonal local-global theorem
  -> orthogonal-basis reduction
  -> general quadratic-form theorem
```

The finite-dimensional induction does not depend on a rank-four theorem. Its
base case is ternary, and each successor step rewrites the coefficient family
as a binary head plus a nonempty tail.

## Ternary base case

The ternary layer has two inputs.

1. `RealClosure/` constructs a same-universe ordered real closure. A maximal
   ordered intermediate field is shown real closed by adjoining square roots of
   nonnegative elements and roots of odd-degree irreducible factors.
2. `Ternary/` translates a ternary diagonal form to a quaternion symbol and
   closes the normalized polynomial Legendre criterion.

The only public bridge out of this layer is
`Ternary.NormalizedLocalGlobal`; finite-dimensional modules consume the final
ternary theorem rather than importing quaternion-residue internals directly.

## Binary-tail induction

After handling zero coefficients, assume that the original coefficient family
has no common strict-sign ordering. For a binary head `a₀, a₁` and a nonempty
tail `ψ`, the proof constructs a
nonzero rational function `c` whose sign at each ordering makes both

```text
<a₀, a₁, c>
<ψ, -c>
```

free of a common strict-sign ordering. The construction proceeds as follows.

1. Remove coefficient squares and choose nonzero squarefree polynomial
   representatives without changing isotropy or strict signs.
2. Collect the finitely many real roots of all representatives.
3. On each complementary interval, compute the required sign of `c`.
4. Build a product of distinct linear factors, inserting a factor precisely at
   the breakpoints where that required sign changes.
5. Transfer the ordinary real-point sign calculation to every ordered real
   closed image using equality of finite cuts.
6. Apply the ternary base theorem to the head and the induction hypothesis to
   the augmented tail, then reconstruct an isotropic vector for the original
   form.

The induction is well-founded on dimension and is reindexed from `Fin n` to an
arbitrary finite type using `Fintype.equivFin`.

## General quadratic forms

For a general finite-dimensional quadratic form `Q`, Mathlib supplies an
orthogonal basis. In that basis, `Q` is isometric to a weighted sum of squares.
The proof applies the total diagonal theorem and transports anisotropy through
the isometry and through scalar extension.

## Module layers

The dependency direction is intentionally one-way.

```text
Core
  -> Sign, Ordering
  -> Polynomial
  -> RealClosure, Ternary
  -> FiniteDimensional
```

- `Core/` contains diagonal and rational-function foundations.
- `Sign/` contains representation-independent strict-sign data.
- `Ordering/` contains orderings and ordering obstructions.
- `Polynomial/` contains polynomial, Laurent, finite-cut, and Legendre linear
  algebra tools.
- `RealClosure/` constructs the ordered real closure used by the ternary base.
- `Ternary/` proves the ternary local-global theorem.
- `FiniteDimensional/` contains compression, induction, and public endpoints.

Large Legendre and quaternion files are split into responsibility-specific
submodules. Ternary reduction propositions live in
`Ternary/Reduction/Basic.lean`, while polynomial normalization lives in
`Ternary/Reduction/PolynomialNormalization.lean`.

## Related documentation

- The complete mathematical proof is available as
  [TeX](docs/ratfunc_witt_local_global_en.tex) and
  [PDF](docs/ratfunc_witt_local_global_en.pdf).
- Build, audit, release, and archive rules live in
  [MAINTENANCE.md](MAINTENANCE.md).
- The [documentation guide](docs/README.md) is the index for all maintained
  documents.
