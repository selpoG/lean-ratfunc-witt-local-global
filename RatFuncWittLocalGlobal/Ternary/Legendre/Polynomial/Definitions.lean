/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Ordering.Obstruction
import RatFuncWittLocalGlobal.Polynomial.NormalForms
import RatFuncWittLocalGlobal.Polynomial.RatFuncReduction
import RatFuncWittLocalGlobal.Polynomial.Gcd
import RatFuncWittLocalGlobal.Polynomial.LaurentPoint
import RatFuncWittLocalGlobal.Polynomial.Positivity
import RatFuncWittLocalGlobal.Polynomial.LegendreLinearAlgebra.Coefficients
import RatFuncWittLocalGlobal.Polynomial.LegendreLinearAlgebra.Remainders
import RatFuncWittLocalGlobal.Polynomial.NonlinearIrreducible.ResidueFields
import RatFuncWittLocalGlobal.Polynomial.NonlinearIrreducible.StandardComplexification
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import Mathlib.Topology.Algebra.Polynomial

/-!
# Polynomial Legendre construction

This module contains the polynomial Legendre construction targets, finite
congruence reductions, boundary cases, and point-ordering bridges used by the
local-global reduction.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

/--
The future polynomial Legendre step, expressed exactly in the shape needed by
the squarefree non-terminal core: after splitting `B` and `C` by their common
factor, construct a nonzero polynomial solution of
`G*r^2 + C₁*q^2 + B₁*d^2 = 0`.
-/
def SquarefreeGcdLegendreConstructionNoOrderingObstruction
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    Prop :=
  ∀ B C : Polynomial R,
    B ≠ 0 →
      C ≠ 0 →
        Squarefree B →
          Squarefree C →
            ¬ NormalizedOrderingObstruction
              (algebraMap (Polynomial R) (RatFunc R) B)
              (algebraMap (Polynomial R) (RatFunc R) C) →
            ¬ IsSquare (-(algebraMap (Polynomial R) (RatFunc R) B)) →
            ¬ IsSquare (-(algebraMap (Polynomial R) (RatFunc R) C)) →
            ∃ s : SquarefreeGcdSplit B C,
              ∃ r q d : Polynomial R,
                (r ≠ 0 ∨ q ≠ 0 ∨ d ≠ 0) ∧
                  s.G * r ^ 2 + s.C₁ * q ^ 2 + s.B₁ * d ^ 2 = 0

/--
The sign hypothesis needed by the Legendre step for the split coefficients:
`G`, `C₁`, and `B₁` do not have a common strict sign in any ordering of
`RatFunc R`.
-/
def SquarefreeGcdSplitNoCommonStrictSign
    {R : Type u} [Field R] {B C : Polynomial R} (s : SquarefreeGcdSplit B C) :
    Prop :=
  ¬ SameStrictSignOrdering
    (algebraMap (Polynomial R) (RatFunc R) s.G)
    (algebraMap (Polynomial R) (RatFunc R) s.C₁)
    (algebraMap (Polynomial R) (RatFunc R) s.B₁)

theorem squarefreeGcdSplitNoCommonStrictSign_of_not_normalizedOrderingObstruction
    {R : Type u} [Field R] {B C : Polynomial R} (s : SquarefreeGcdSplit B C)
    (hno : ¬ NormalizedOrderingObstruction
      (algebraMap (Polynomial R) (RatFunc R) B)
      (algebraMap (Polynomial R) (RatFunc R) C)) :
    SquarefreeGcdSplitNoCommonStrictSign s := by
  intro hsame
  let φ := algebraMap (Polynomial R) (RatFunc R)
  have hC : φ C = φ s.G * φ s.C₁ := by
    simpa [φ, map_mul] using congrArg φ s.hC
  have hB : φ B = φ s.G * φ s.B₁ := by
    simpa [φ, map_mul] using congrArg φ s.hB
  have hCB : NormalizedOrderingObstruction (φ C) (φ B) :=
    normalizedOrderingObstruction_of_sameStrictSign_factors hC hB hsame
  exact hno ((normalizedOrderingObstruction_swap).mpr hCB)

/--
The finite local square-congruence hypotheses in the polynomial Legendre
theorem for the ternary form `A*x^2 + B*y^2 + C*z^2`.
-/
def PolynomialLegendreLocalConditions
    {R : Type u} [CommRing R] (A B C : Polynomial R) : Prop :=
  (∀ π : Polynomial R, Irreducible π → π ∣ A → IsSquareMod π (-(B * C))) ∧
    (∀ π : Polynomial R, Irreducible π → π ∣ B → IsSquareMod π (-(A * C))) ∧
      (∀ π : Polynomial R, Irreducible π → π ∣ C → IsSquareMod π (-(A * B)))

/--
A stronger but often easier-to-assemble version of the Legendre congruence
conditions: the required element is square modulo the whole coefficient, not
only modulo each irreducible factor.
-/
def PolynomialLegendreWholeModConditions
    {R : Type u} [CommRing R] (A B C : Polynomial R) : Prop :=
  IsSquareMod A (-(B * C)) ∧
    IsSquareMod B (-(A * C)) ∧
      IsSquareMod C (-(A * B))

theorem polynomialLegendreLocalConditions_of_wholeModConditions
    {R : Type u} [CommRing R] {A B C : Polynomial R}
    (hwhole : PolynomialLegendreWholeModConditions A B C) :
    PolynomialLegendreLocalConditions A B C := by
  refine ⟨?_, ?_, ?_⟩
  · intro π _hirr hπA
    exact hwhole.1.of_dvd hπA
  · intro π _hirr hπB
    exact hwhole.2.1.of_dvd hπB
  · intro π _hirr hπC
    exact hwhole.2.2.of_dvd hπC

theorem polynomialLegendreWholeModConditions_of_localConditions
    {R : Type u} [Field R] {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hAsq : Squarefree A) (hBsq : Squarefree B) (hCsq : Squarefree C)
    (hlocal : PolynomialLegendreLocalConditions A B C) :
    PolynomialLegendreWholeModConditions A B C := by
  refine ⟨?_, ?_, ?_⟩
  · exact isSquareMod_of_forall_irreducible_dvd_of_squarefree hA0 hAsq hlocal.1
  · exact isSquareMod_of_forall_irreducible_dvd_of_squarefree hB0 hBsq hlocal.2.1
  · exact isSquareMod_of_forall_irreducible_dvd_of_squarefree hC0 hCsq hlocal.2.2

/-- Whole-modulus congruence conditions for the coefficients from a gcd split. -/
def SquarefreeGcdSplitLegendreWholeModConditions
    {R : Type u} [Field R] {B C : Polynomial R} (s : SquarefreeGcdSplit B C) :
    Prop :=
  PolynomialLegendreWholeModConditions s.G s.C₁ s.B₁

theorem squarefreeGcdSplitLegendreLocalConditions_of_wholeModConditions
    {R : Type u} [Field R] {B C : Polynomial R} {s : SquarefreeGcdSplit B C}
    (hwhole : SquarefreeGcdSplitLegendreWholeModConditions s) :
    PolynomialLegendreLocalConditions s.G s.C₁ s.B₁ :=
  polynomialLegendreLocalConditions_of_wholeModConditions hwhole

theorem squarefreeGcdSplitLegendreWholeModConditions_of_factor_mod
    {R : Type u} [Field R] {B C : Polynomial R} (s : SquarefreeGcdSplit B C)
    (hG : IsSquareMod s.G (-(s.C₁ * s.B₁)))
    (hC₁ : IsSquareMod s.C₁ (-B))
    (hB₁ : IsSquareMod s.B₁ (-C)) :
    SquarefreeGcdSplitLegendreWholeModConditions s := by
  refine ⟨hG, ?_, ?_⟩
  · exact s.isSquareMod_neg_G_mul_B₁_of_neg_B hC₁
  · exact s.isSquareMod_neg_G_mul_C₁_of_neg_C hB₁

theorem squarefreeGcdSplitLegendreLocalConditions_of_factor_mod
    {R : Type u} [Field R] {B C : Polynomial R} (s : SquarefreeGcdSplit B C)
    (hG : IsSquareMod s.G (-(s.C₁ * s.B₁)))
    (hC₁ : IsSquareMod s.C₁ (-B))
    (hB₁ : IsSquareMod s.B₁ (-C)) :
    PolynomialLegendreLocalConditions s.G s.C₁ s.B₁ :=
  squarefreeGcdSplitLegendreLocalConditions_of_wholeModConditions
    (squarefreeGcdSplitLegendreWholeModConditions_of_factor_mod s hG hC₁ hB₁)

/--
The reusable polynomial Legendre construction over `R[X]`, stated in the
orientation used by the gcd split.
-/
def PolynomialLegendreConstruction
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    Prop :=
  ∀ A B C : Polynomial R,
    A ≠ 0 →
      B ≠ 0 →
        C ≠ 0 →
          Squarefree A →
            Squarefree B →
              Squarefree C →
                IsCoprime A B →
                  IsCoprime A C →
                    IsCoprime B C →
                      PolynomialLegendreLocalConditions A B C →
                        ¬ SameStrictSignOrdering
                          (algebraMap (Polynomial R) (RatFunc R) A)
                          (algebraMap (Polynomial R) (RatFunc R) B)
                          (algebraMap (Polynomial R) (RatFunc R) C) →
                        ∃ x y z : Polynomial R,
                          (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
                            A * x ^ 2 + B * y ^ 2 + C * z ^ 2 = 0

end RatFunc

end RatFuncWittLocalGlobal
