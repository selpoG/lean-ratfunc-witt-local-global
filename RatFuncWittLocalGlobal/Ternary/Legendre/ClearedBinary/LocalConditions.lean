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
import RatFuncWittLocalGlobal.Ternary.Legendre.Polynomial.Definitions
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
# Cleared binary and squarefree reductions

This module contains the cleared binary targets, squarefree reduction, and
gcd-Legendre-to-binary bridge used by the local-global theorem.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

/--
The cleared binary target for the right-hand coefficient:
`p^2 + C*q^2 = (-B)*d^2`, unless `-C` is already a square in `RatFunc R`.
-/
def ClearedBinaryOrSquareRight
    (R : Type u) [Field R] (B C : Polynomial R) : Prop :=
  (∃ p q d : Polynomial R,
    d ≠ 0 ∧
      (algebraMap (Polynomial R) (RatFunc R) p) ^ 2 +
        algebraMap (Polynomial R) (RatFunc R) C *
          (algebraMap (Polynomial R) (RatFunc R) q) ^ 2 =
        (-(algebraMap (Polynomial R) (RatFunc R) B)) *
          (algebraMap (Polynomial R) (RatFunc R) d) ^ 2) ∨
    IsSquare (-(algebraMap (Polynomial R) (RatFunc R) C))

/-- The non-terminal right-oriented cleared binary identity. -/
def ClearedBinaryRight
    (R : Type u) [Field R] (B C : Polynomial R) : Prop :=
  ∃ p q d : Polynomial R,
    d ≠ 0 ∧
      (algebraMap (Polynomial R) (RatFunc R) p) ^ 2 +
        algebraMap (Polynomial R) (RatFunc R) C *
          (algebraMap (Polynomial R) (RatFunc R) q) ^ 2 =
        (-(algebraMap (Polynomial R) (RatFunc R) B)) *
          (algebraMap (Polynomial R) (RatFunc R) d) ^ 2

/--
The remaining right-oriented cleared binary construction problem for nonzero
polynomial coefficients.
-/
def ClearedBinaryConstructionRight
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    Prop :=
  ∀ B C : Polynomial R,
    B ≠ 0 →
      C ≠ 0 →
        NormalizedSignObstructionFree.{u, v}
          (algebraMap (Polynomial R) (RatFunc R) B)
          (algebraMap (Polynomial R) (RatFunc R) C) →
        ClearedBinaryOrSquareRight R B C

/--
The right-oriented core construction stated using nonexistence of an explicit
positive-positive real closed target witness.
-/
def ClearedBinaryConstructionRightNoObstruction
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    Prop :=
  ∀ B C : Polynomial R,
    B ≠ 0 →
      C ≠ 0 →
        ¬ HasNormalizedSignObstruction.{u, v}
          (algebraMap (Polynomial R) (RatFunc R) B)
          (algebraMap (Polynomial R) (RatFunc R) C) →
        ClearedBinaryOrSquareRight R B C

/--
The right-oriented core construction restricted to squarefree nonzero
polynomial coefficients.
-/
def SquarefreeClearedBinaryConstructionRightNoObstruction
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    Prop :=
  ∀ B C : Polynomial R,
    B ≠ 0 →
      C ≠ 0 →
        Squarefree B →
          Squarefree C →
            ¬ HasNormalizedSignObstruction.{u, v}
              (algebraMap (Polynomial R) (RatFunc R) B)
              (algebraMap (Polynomial R) (RatFunc R) C) →
            ClearedBinaryOrSquareRight R B C

/--
The right-oriented squarefree core after removing the terminal square branch.
If `-C` is already a square, `ClearedBinaryOrSquareRight` is immediate; this
predicate records only the genuinely binary construction case.
-/
def SquarefreeBinaryConstructionRightNoObstruction
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    Prop :=
  ∀ B C : Polynomial R,
    B ≠ 0 →
      C ≠ 0 →
        Squarefree B →
          Squarefree C →
            ¬ HasNormalizedSignObstruction.{u, v}
              (algebraMap (Polynomial R) (RatFunc R) B)
              (algebraMap (Polynomial R) (RatFunc R) C) →
            ¬ IsSquare (-(algebraMap (Polynomial R) (RatFunc R) C)) →
            ClearedBinaryRight R B C

/--
The right-oriented squarefree binary core after excluding both terminal square
cases.
-/
def SquarefreeNonterminalBinaryConstructionRightNoObstruction
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    Prop :=
  ∀ B C : Polynomial R,
    B ≠ 0 →
      C ≠ 0 →
        Squarefree B →
          Squarefree C →
            ¬ HasNormalizedSignObstruction.{u, v}
              (algebraMap (Polynomial R) (RatFunc R) B)
              (algebraMap (Polynomial R) (RatFunc R) C) →
            ¬ IsSquare (-(algebraMap (Polynomial R) (RatFunc R) B)) →
            ¬ IsSquare (-(algebraMap (Polynomial R) (RatFunc R) C)) →
            ClearedBinaryRight R B C

/--
The right-oriented non-terminal squarefree core with the abstract real-closed
target obstruction replaced by an ordering obstruction on `RatFunc R`.
-/
def SquarefreeNonterminalBinaryConstructionRightNoOrderingObstruction
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
            ClearedBinaryRight R B C

/--
The remaining local-congruence extraction needed after the gcd split.  This is
the part that will be proved from root orderings and squarefree hypotheses.
-/
def SquarefreeGcdLegendreLocalConditionsNoOrderingObstruction
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
              PolynomialLegendreLocalConditions s.G s.C₁ s.B₁

/--
The concrete factor-modulus obligations that remain for the gcd split.  These
are the conditions expected to come from explicit root orderings.
-/
def SquarefreeGcdLegendreFactorModConditionsNoOrderingObstruction
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
              IsSquareMod s.G (-(s.C₁ * s.B₁)) ∧
                IsSquareMod s.C₁ (-B) ∧
                  IsSquareMod s.B₁ (-C)

/--
The same local obligations stated for arbitrary irreducible divisors of the
split coefficients, rather than normalized factors.
-/
def SquarefreeGcdLegendreIrreducibleDivisorConditionsNoOrderingObstruction
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
              (∀ π : Polynomial R,
                Irreducible π → π ∣ s.G → IsSquareMod π (-(s.C₁ * s.B₁))) ∧
                (∀ π : Polynomial R,
                  Irreducible π → π ∣ s.C₁ → IsSquareMod π (-B)) ∧
                  (∀ π : Polynomial R,
                    Irreducible π → π ∣ s.B₁ → IsSquareMod π (-C))

/--
The irreducible-divisor obligations split into the two cases used by the
local arguments.  Linear factors only require a root at which the relevant
evaluation is nonnegative; nonlinear factors are left as direct square-mod
obligations.
-/
def SquarefreeGcdLegendreLinearAndNonlinearDivisorConditionsNoOrderingObstruction
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
              (∀ π : Polynomial R,
                Irreducible π → π ∣ s.G → π.natDegree = 1 →
                  ∃ a : R,
                    Associated π (Polynomial.X - Polynomial.C a) ∧
                      0 ≤ (-(s.C₁ * s.B₁)).eval a) ∧
                (∀ π : Polynomial R,
                  Irreducible π → π ∣ s.G → π.natDegree ≠ 1 →
                    IsSquareMod π (-(s.C₁ * s.B₁))) ∧
                  (∀ π : Polynomial R,
                    Irreducible π → π ∣ s.C₁ → π.natDegree = 1 →
                      ∃ a : R,
                        Associated π (Polynomial.X - Polynomial.C a) ∧
                          0 ≤ (-B).eval a) ∧
                    (∀ π : Polynomial R,
                      Irreducible π → π ∣ s.C₁ → π.natDegree ≠ 1 →
                        IsSquareMod π (-B)) ∧
                      (∀ π : Polynomial R,
                        Irreducible π → π ∣ s.B₁ → π.natDegree = 1 →
                          ∃ a : R,
                            Associated π (Polynomial.X - Polynomial.C a) ∧
                              0 ≤ (-C).eval a) ∧
                        (∀ π : Polynomial R,
                          Irreducible π → π ∣ s.B₁ → π.natDegree ≠ 1 →
                            IsSquareMod π (-C))

/--
The linear part of the irreducible-divisor obligations.  This is the part to
be proved from explicit left/right root orderings.
-/
def SquarefreeGcdLegendreLinearDivisorSignConditionsNoOrderingObstruction
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
              (∀ π : Polynomial R,
                Irreducible π → π ∣ s.G → π.natDegree = 1 →
                  ∃ a : R,
                    Associated π (Polynomial.X - Polynomial.C a) ∧
                      0 ≤ (-(s.C₁ * s.B₁)).eval a) ∧
                (∀ π : Polynomial R,
                  Irreducible π → π ∣ s.C₁ → π.natDegree = 1 →
                    ∃ a : R,
                      Associated π (Polynomial.X - Polynomial.C a) ∧
                        0 ≤ (-B).eval a) ∧
                  (∀ π : Polynomial R,
                    Irreducible π → π ∣ s.B₁ → π.natDegree = 1 →
                      ∃ a : R,
                        Associated π (Polynomial.X - Polynomial.C a) ∧
                          0 ≤ (-C).eval a)

/--
The explicit root-ordering principles needed for linear factors: if the
forbidden sign occurs at the corresponding root, then it creates a normalized
ordering obstruction for the original pair `B,C`.
-/
def SquarefreeGcdLegendreLinearRootObstructionPrinciples
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    Prop :=
  ∀ B C : Polynomial R,
    B ≠ 0 →
      C ≠ 0 →
        Squarefree B →
          Squarefree C →
            ∀ s : SquarefreeGcdSplit B C,
              (∀ π : Polynomial R, ∀ a : R,
                Irreducible π → π ∣ s.G →
                  Associated π (Polynomial.X - Polynomial.C a) →
                    0 < (s.C₁ * s.B₁).eval a →
                      NormalizedOrderingObstruction
                        (algebraMap (Polynomial R) (RatFunc R) B)
                        (algebraMap (Polynomial R) (RatFunc R) C)) ∧
                (∀ π : Polynomial R, ∀ a : R,
                  Irreducible π → π ∣ s.C₁ →
                    Associated π (Polynomial.X - Polynomial.C a) →
                      0 < B.eval a →
                        NormalizedOrderingObstruction
                          (algebraMap (Polynomial R) (RatFunc R) B)
                          (algebraMap (Polynomial R) (RatFunc R) C)) ∧
                  (∀ π : Polynomial R, ∀ a : R,
                    Irreducible π → π ∣ s.B₁ →
                      Associated π (Polynomial.X - Polynomial.C a) →
                      0 < C.eval a →
                        NormalizedOrderingObstruction
                          (algebraMap (Polynomial R) (RatFunc R) B)
                          (algebraMap (Polynomial R) (RatFunc R) C))

/--
The ordered-field version of the linear root principles.  This is closer to
the explicit local-ordering construction: each bad sign at a linear factor
should supply an order on `RatFunc R` where the original pair `B,C` is positive.
-/
def SquarefreeGcdLegendreLinearRootOrderedPosPrinciples
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    Prop :=
  ∀ B C : Polynomial R,
    B ≠ 0 →
      C ≠ 0 →
        Squarefree B →
          Squarefree C →
            ∀ s : SquarefreeGcdSplit B C,
              (∀ π : Polynomial R, ∀ a : R,
                Irreducible π → π ∣ s.G →
                  Associated π (Polynomial.X - Polynomial.C a) →
                    0 < (s.C₁ * s.B₁).eval a →
                      Nonempty (OrderedRatFuncPositivePair
                        (algebraMap (Polynomial R) (RatFunc R) B)
                        (algebraMap (Polynomial R) (RatFunc R) C))) ∧
                (∀ π : Polynomial R, ∀ a : R,
                  Irreducible π → π ∣ s.C₁ →
                    Associated π (Polynomial.X - Polynomial.C a) →
                      0 < B.eval a →
                        Nonempty (OrderedRatFuncPositivePair
                          (algebraMap (Polynomial R) (RatFunc R) B)
                          (algebraMap (Polynomial R) (RatFunc R) C))) ∧
                  (∀ π : Polynomial R, ∀ a : R,
                    Irreducible π → π ∣ s.B₁ →
                      Associated π (Polynomial.X - Polynomial.C a) →
                        0 < C.eval a →
                          Nonempty (OrderedRatFuncPositivePair
                            (algebraMap (Polynomial R) (RatFunc R) B)
                            (algebraMap (Polynomial R) (RatFunc R) C)))

theorem linearRootOrderedPosPrinciples_of_homPosPrinciples
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hhom : SquarefreeGcdLegendreLinearRootHomPosPrinciples.{u, v} R) :
    SquarefreeGcdLegendreLinearRootOrderedPosPrinciples R := by
  intro B C hB0 hC0 hBsq hCsq s
  rcases hhom B C hB0 hC0 hBsq hCsq s with
    ⟨hGhom, hC₁hom, hB₁hom⟩
  refine ⟨?_, ?_, ?_⟩
  · intro π a hπ hπG hlin hpos
    rcases hGhom π a hπ hπG hlin hpos with
      ⟨K, hKfield, hKorder, hKstrict, f, hBpos, hCpos⟩
    let _ : Field K := hKfield
    let _ : LinearOrder K := hKorder
    let _ : IsStrictOrderedRing K := hKstrict
    exact orderedRatFuncPositivePair_of_normalizedOrderingObstruction
      (normalizedOrderingObstruction_of_hom_pos f hBpos hCpos)
  · intro π a hπ hπC₁ hlin hpos
    rcases hC₁hom π a hπ hπC₁ hlin hpos with
      ⟨K, hKfield, hKorder, hKstrict, f, hBpos, hCpos⟩
    let _ : Field K := hKfield
    let _ : LinearOrder K := hKorder
    let _ : IsStrictOrderedRing K := hKstrict
    exact orderedRatFuncPositivePair_of_normalizedOrderingObstruction
      (normalizedOrderingObstruction_of_hom_pos f hBpos hCpos)
  · intro π a hπ hπB₁ hlin hpos
    rcases hB₁hom π a hπ hπB₁ hlin hpos with
      ⟨K, hKfield, hKorder, hKstrict, f, hBpos, hCpos⟩
    let _ : Field K := hKfield
    let _ : LinearOrder K := hKorder
    let _ : IsStrictOrderedRing K := hKstrict
    exact orderedRatFuncPositivePair_of_normalizedOrderingObstruction
      (normalizedOrderingObstruction_of_hom_pos f hBpos hCpos)

/-- Laurent-series point-sign constructions supply the ordered linear-root principles. -/
theorem squarefreeGcdLegendreLinearRootOrderedPosPrinciples_laurentSeries
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    SquarefreeGcdLegendreLinearRootOrderedPosPrinciples R :=
  linearRootOrderedPosPrinciples_of_homPosPrinciples
    (squarefreeGcdLegendreLinearRootHomPosPrinciples_laurentSeries R)

theorem linearRootObstructionPrinciples_of_orderedPosPrinciples
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hordered : SquarefreeGcdLegendreLinearRootOrderedPosPrinciples R) :
    SquarefreeGcdLegendreLinearRootObstructionPrinciples R := by
  intro B C hB0 hC0 hBsq hCsq s
  rcases hordered B C hB0 hC0 hBsq hCsq s with
    ⟨hGordered, hC₁ordered, hB₁ordered⟩
  exact ⟨
    (fun π a hπ hπG hlin hpos =>
      let ⟨w⟩ := hGordered π a hπ hπG hlin hpos
      normalizedOrderingObstruction_of_orderedRatFuncPositivePair w),
    (fun π a hπ hπC₁ hlin hpos =>
      let ⟨w⟩ := hC₁ordered π a hπ hπC₁ hlin hpos
      normalizedOrderingObstruction_of_orderedRatFuncPositivePair w),
    (fun π a hπ hπB₁ hlin hpos =>
      let ⟨w⟩ := hB₁ordered π a hπ hπB₁ hlin hpos
      normalizedOrderingObstruction_of_orderedRatFuncPositivePair w)⟩

theorem linearDivisorSignConditionsNoOrderingObstruction_of_rootObstructionPrinciples
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hroot : SquarefreeGcdLegendreLinearRootObstructionPrinciples R) :
    SquarefreeGcdLegendreLinearDivisorSignConditionsNoOrderingObstruction R := by
  intro B C hB0 hC0 hBsq hCsq hno _hnotB _hnotC
  rcases exists_squarefreeGcdSplit hB0 hC0 hBsq hCsq with ⟨s⟩
  rcases hroot B C hB0 hC0 hBsq hCsq s with ⟨hGroot, hC₁root, hB₁root⟩
  refine ⟨s, ?_, ?_, ?_⟩
  · intro π hπ hπG hdeg
    rcases exists_associated_X_sub_C_of_irreducible_of_natDegree_eq_one hπ hdeg with
      ⟨a, hlin⟩
    refine ⟨a, hlin, ?_⟩
    by_contra hnonneg
    have hlt : (-(s.C₁ * s.B₁)).eval a < 0 := lt_of_not_ge hnonneg
    have hpos : 0 < (s.C₁ * s.B₁).eval a := by
      rw [Polynomial.eval_neg] at hlt
      linarith
    exact hno (hGroot π a hπ hπG hlin hpos)
  · intro π hπ hπC₁ hdeg
    rcases exists_associated_X_sub_C_of_irreducible_of_natDegree_eq_one hπ hdeg with
      ⟨a, hlin⟩
    refine ⟨a, hlin, ?_⟩
    by_contra hnonneg
    have hlt : (-B).eval a < 0 := lt_of_not_ge hnonneg
    have hpos : 0 < B.eval a := by
      rw [Polynomial.eval_neg] at hlt
      linarith
    exact hno (hC₁root π a hπ hπC₁ hlin hpos)
  · intro π hπ hπB₁ hdeg
    rcases exists_associated_X_sub_C_of_irreducible_of_natDegree_eq_one hπ hdeg with
      ⟨a, hlin⟩
    refine ⟨a, hlin, ?_⟩
    by_contra hnonneg
    have hlt : (-C).eval a < 0 := lt_of_not_ge hnonneg
    have hpos : 0 < C.eval a := by
      rw [Polynomial.eval_neg] at hlt
      linarith
    exact hno (hB₁root π a hπ hπB₁ hlin hpos)

/--
The Laurent-series point-sign construction closes the linear factor branch
directly.  At a linear factor, a negative target evaluation would turn the
corresponding product (or coefficient) evaluation positive; the ordered
positive pair supplied by the Laurent root principle then contradicts the
assumed absence of a normalized ordering obstruction.
-/
theorem squarefreeGcdLegendreLinearDivisorSignConditionsNoOrderingObstruction_laurentSeries
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    SquarefreeGcdLegendreLinearDivisorSignConditionsNoOrderingObstruction R := by
  intro B C hB0 hC0 hBsq hCsq hno _hnotB _hnotC
  rcases exists_squarefreeGcdSplit hB0 hC0 hBsq hCsq with ⟨s⟩
  rcases (squarefreeGcdLegendreLinearRootOrderedPosPrinciples_laurentSeries R)
      B C hB0 hC0 hBsq hCsq s with
    ⟨hGordered, hC₁ordered, hB₁ordered⟩
  refine ⟨s, ?_, ?_, ?_⟩
  · intro π hπ hπG hdeg
    rcases exists_associated_X_sub_C_of_irreducible_of_natDegree_eq_one hπ hdeg with
      ⟨a, hlin⟩
    refine ⟨a, hlin, ?_⟩
    by_contra hnonneg
    have hlt : (-(s.C₁ * s.B₁)).eval a < 0 := lt_of_not_ge hnonneg
    have hpos : 0 < (s.C₁ * s.B₁).eval a := by
      rw [Polynomial.eval_neg] at hlt
      linarith
    rcases hGordered π a hπ hπG hlin hpos with ⟨w⟩
    exact hno (normalizedOrderingObstruction_of_orderedRatFuncPositivePair w)
  · intro π hπ hπC₁ hdeg
    rcases exists_associated_X_sub_C_of_irreducible_of_natDegree_eq_one hπ hdeg with
      ⟨a, hlin⟩
    refine ⟨a, hlin, ?_⟩
    by_contra hnonneg
    have hlt : (-B).eval a < 0 := lt_of_not_ge hnonneg
    have hpos : 0 < B.eval a := by
      rw [Polynomial.eval_neg] at hlt
      linarith
    rcases hC₁ordered π a hπ hπC₁ hlin hpos with ⟨w⟩
    exact hno (normalizedOrderingObstruction_of_orderedRatFuncPositivePair w)
  · intro π hπ hπB₁ hdeg
    rcases exists_associated_X_sub_C_of_irreducible_of_natDegree_eq_one hπ hdeg with
      ⟨a, hlin⟩
    refine ⟨a, hlin, ?_⟩
    by_contra hnonneg
    have hlt : (-C).eval a < 0 := lt_of_not_ge hnonneg
    have hpos : 0 < C.eval a := by
      rw [Polynomial.eval_neg] at hlt
      linarith
    rcases hB₁ordered π a hπ hπB₁ hlin hpos with ⟨w⟩
    exact hno (normalizedOrderingObstruction_of_orderedRatFuncPositivePair w)

theorem linearAndNonlinearDivisorConditionsNoOrderingObstruction_of_linearSigns
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hlinear : SquarefreeGcdLegendreLinearDivisorSignConditionsNoOrderingObstruction R)
    (hnonlinear : NonlinearIrreducibleDivisorSquareMod R) :
    SquarefreeGcdLegendreLinearAndNonlinearDivisorConditionsNoOrderingObstruction R := by
  intro B C hB0 hC0 hBsq hCsq hno hnotB hnotC
  rcases hlinear B C hB0 hC0 hBsq hCsq hno hnotB hnotC with
    ⟨s, hGlin, hC₁lin, hB₁lin⟩
  exact ⟨s,
    hGlin,
    (fun π hπ _hπG hdeg => hnonlinear π (-(s.C₁ * s.B₁)) hπ hdeg),
    hC₁lin,
    (fun π hπ _hπC₁ hdeg => hnonlinear π (-B) hπ hdeg),
    hB₁lin,
    (fun π hπ _hπB₁ hdeg => hnonlinear π (-C) hπ hdeg)⟩

theorem squarefreeGcdLegendreFactorModConditionsNoOrderingObstruction_of_irreducibleDivisors
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hirrDivisors : SquarefreeGcdLegendreIrreducibleDivisorConditionsNoOrderingObstruction R) :
    SquarefreeGcdLegendreFactorModConditionsNoOrderingObstruction R := by
  classical
  intro B C hB0 hC0 hBsq hCsq hno hnotB hnotC
  rcases hirrDivisors B C hB0 hC0 hBsq hCsq hno hnotB hnotC with
    ⟨s, hG, hC₁, hB₁⟩
  exact ⟨s,
    isSquareMod_of_forall_irreducible_dvd_of_squarefree s.G_ne_zero s.squarefree_G hG,
    isSquareMod_of_forall_irreducible_dvd_of_squarefree s.C₁_ne_zero s.squarefree_C₁ hC₁,
    isSquareMod_of_forall_irreducible_dvd_of_squarefree s.B₁_ne_zero s.squarefree_B₁ hB₁⟩

theorem
    irreducibleDivisorConditionsNoOrderingObstruction_of_splitDivisors
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hlocal :
      SquarefreeGcdLegendreLinearAndNonlinearDivisorConditionsNoOrderingObstruction R) :
    SquarefreeGcdLegendreIrreducibleDivisorConditionsNoOrderingObstruction R := by
  classical
  intro B C hB0 hC0 hBsq hCsq hno hnotB hnotC
  rcases hlocal B C hB0 hC0 hBsq hCsq hno hnotB hnotC with
    ⟨s, hGlin, hGnonlin, hC₁lin, hC₁nonlin, hB₁lin, hB₁nonlin⟩
  refine ⟨s, ?_, ?_, ?_⟩
  · intro π hπ hπG
    by_cases hdeg : π.natDegree = 1
    · rcases hGlin π hπ hπG hdeg with ⟨a, hlin, hnonneg⟩
      exact
        s.isSquareMod_neg_C₁_mul_B₁_of_irreducible_dvd_G_of_linear_of_nonneg_eval
          hπ hπG hlin hnonneg
    · exact hGnonlin π hπ hπG hdeg
  · intro π hπ hπC₁
    by_cases hdeg : π.natDegree = 1
    · rcases hC₁lin π hπ hπC₁ hdeg with ⟨a, hlin, hnonneg⟩
      exact
        s.isSquareMod_neg_B_of_irreducible_dvd_C₁_of_linear_of_nonneg_eval
          hπ hπC₁ hlin hnonneg
    · exact hC₁nonlin π hπ hπC₁ hdeg
  · intro π hπ hπB₁
    by_cases hdeg : π.natDegree = 1
    · rcases hB₁lin π hπ hπB₁ hdeg with ⟨a, hlin, hnonneg⟩
      exact
        s.isSquareMod_neg_C_of_irreducible_dvd_B₁_of_linear_of_nonneg_eval
          hπ hπB₁ hlin hnonneg
    · exact hB₁nonlin π hπ hπB₁ hdeg

theorem squarefreeGcdLegendreFactorModConditionsNoOrderingObstruction_of_splitDivisors
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hlocal :
      SquarefreeGcdLegendreLinearAndNonlinearDivisorConditionsNoOrderingObstruction R) :
    SquarefreeGcdLegendreFactorModConditionsNoOrderingObstruction R :=
  squarefreeGcdLegendreFactorModConditionsNoOrderingObstruction_of_irreducibleDivisors
    (irreducibleDivisorConditionsNoOrderingObstruction_of_splitDivisors hlocal)

theorem squarefreeGcdLegendreLocalConditionsNoOrderingObstruction_of_factorMod
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hfactor : SquarefreeGcdLegendreFactorModConditionsNoOrderingObstruction R) :
    SquarefreeGcdLegendreLocalConditionsNoOrderingObstruction R := by
  intro B C hB0 hC0 hBsq hCsq hno hnotB hnotC
  rcases hfactor B C hB0 hC0 hBsq hCsq hno hnotB hnotC with
    ⟨s, hG, hC₁, hB₁⟩
  exact ⟨s, squarefreeGcdSplitLegendreLocalConditions_of_factor_mod s hG hC₁ hB₁⟩

/--
The direct Laurent-series linear branch is consumable by the existing
linear-plus-nonlinear local-condition assembly; only the nonlinear square-mod
input remains in this slice.
-/
theorem squarefreeGcdLegendreLocalConditionsNoOrderingObstruction_of_laurentSeriesLinearSigns
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hnonlinear : NonlinearIrreducibleDivisorSquareMod R) :
    SquarefreeGcdLegendreLocalConditionsNoOrderingObstruction R :=
  squarefreeGcdLegendreLocalConditionsNoOrderingObstruction_of_factorMod
    (squarefreeGcdLegendreFactorModConditionsNoOrderingObstruction_of_splitDivisors
      (linearAndNonlinearDivisorConditionsNoOrderingObstruction_of_linearSigns
        (squarefreeGcdLegendreLinearDivisorSignConditionsNoOrderingObstruction_laurentSeries R)
        hnonlinear))

theorem squarefreeGcdLegendreLocalConditionsNoOrderingObstruction_of_realClosed
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    SquarefreeGcdLegendreLocalConditionsNoOrderingObstruction R :=
  squarefreeGcdLegendreLocalConditionsNoOrderingObstruction_of_laurentSeriesLinearSigns
    (nonlinearIrreducibleDivisorSquareMod_of_realClosed (R := R))

theorem squarefreeGcdLegendreConstructionNoOrderingObstruction_of_polynomialLegendre
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hlegendre : PolynomialLegendreConstruction R)
    (hlocal : SquarefreeGcdLegendreLocalConditionsNoOrderingObstruction R) :
    SquarefreeGcdLegendreConstructionNoOrderingObstruction R := by
  intro B C hB0 hC0 hBsq hCsq hno hnotB hnotC
  rcases hlocal B C hB0 hC0 hBsq hCsq hno hnotB hnotC with ⟨s, hconds⟩
  rcases hlegendre s.G s.C₁ s.B₁
      s.G_ne_zero s.C₁_ne_zero s.B₁_ne_zero
      s.squarefree_G s.squarefree_C₁ s.squarefree_B₁
      s.coprime_G_C₁ s.coprime_G_B₁ s.coprime_B₁_C₁.symm
      hconds
      (squarefreeGcdSplitNoCommonStrictSign_of_not_normalizedOrderingObstruction s hno) with
    ⟨r, q, d, hne, hzero⟩
  exact ⟨s, r, q, d, hne, hzero⟩

theorem squarefreeGcdLegendreConstructionNoOrderingObstruction_of_polynomialLegendre_of_factorMod
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hlegendre : PolynomialLegendreConstruction R)
    (hfactor : SquarefreeGcdLegendreFactorModConditionsNoOrderingObstruction R) :
    SquarefreeGcdLegendreConstructionNoOrderingObstruction R :=
  squarefreeGcdLegendreConstructionNoOrderingObstruction_of_polynomialLegendre
    hlegendre
    (squarefreeGcdLegendreLocalConditionsNoOrderingObstruction_of_factorMod hfactor)

end RatFunc
end RatFuncWittLocalGlobal
