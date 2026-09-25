/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Ternary.Quaternion.Polynomial.Detection

/-!
# Polynomial quaternion endpoint

This module contains the consumers used by the public ternary proof.
-/

namespace RatFuncWittLocalGlobal

universe u

variable {R : Type u}

/--
Polynomial wrapper using the polynomial-specialized quaternion residue criterion
and an already packaged residue-triviality input.
-/
theorem polynomial_sqfree_pairwise_isotropic_of_polyQuaternionCriterion
    [LinearOrder R] [Field R]
    (hcriterion : PolynomialTernaryQuaternionSplitCriterion (R := R))
    {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hAsq : Squarefree A) (hBsq : Squarefree B) (hCsq : Squarefree C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hBC : IsCoprime B C)
    (hres :
      PolynomialTernaryQuaternionResiduesTrivialFor
        (PolynomialTernaryFiniteResidueTrivial A B C)
        (PolynomialTernaryNoCommonStrictSignAtInfinity A B C) A B C)
    (hno :
      ¬ RatFunc.SameStrictSignOrdering
        (algebraMap (Polynomial R) (RatFunc R) A)
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C)) :
    Diagonal.TernaryIsotropic
      (algebraMap (Polynomial R) (RatFunc R) A)
      (algebraMap (Polynomial R) (RatFunc R) B)
      (algebraMap (Polynomial R) (RatFunc R) C) := by
  have hAφ : algebraMap (Polynomial R) (RatFunc R) A ≠ 0 :=
    _root_.RatFunc.algebraMap_ne_zero hA0
  have hsplit :
      QuaternionSymbolSplit
        (polynomialTernaryQuaternionCoeff A B)
        (polynomialTernaryQuaternionCoeff A C) :=
    polynomialQuaternionSymbolSplit_of_polyQuaternionCriterion
      hcriterion hA0 hB0 hC0 hAsq hBsq hCsq hAB hAC hBC hres hno
  exact
    (Diagonal.ternary_isotropic_iff_quaternionSymbolSplit_normalize_first
      hAφ).mpr (by
        change
          QuaternionSymbolSplit
            (polynomialTernaryQuaternionCoeff A B)
            (polynomialTernaryQuaternionCoeff A C)
        exact hsplit)

/--
Laurent-infinity polynomial wrapper using the polynomial-specialized
quaternion residue criterion.
-/
theorem polynomial_sqfree_pairwise_isotropic_of_polyQuaternionCriterion_laurentInfinity
    [LinearOrder R] [Field R] [IsStrictOrderedRing R]
    (hcriterion : PolynomialTernaryQuaternionSplitCriterion (R := R))
    {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hAsq : Squarefree A) (hBsq : Squarefree B) (hCsq : Squarefree C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hBC : IsCoprime B C)
    (hfinite : RatFunc.PolynomialLegendreLocalConditions A B C)
    (hno :
      ¬ RatFunc.SameStrictSignOrdering
        (algebraMap (Polynomial R) (RatFunc R) A)
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C)) :
    Diagonal.TernaryIsotropic
      (algebraMap (Polynomial R) (RatFunc R) A)
      (algebraMap (Polynomial R) (RatFunc R) B)
      (algebraMap (Polynomial R) (RatFunc R) C) :=
  polynomial_sqfree_pairwise_isotropic_of_polyQuaternionCriterion
    hcriterion
    hA0 hB0 hC0 hAsq hBsq hCsq hAB hAC hBC
    (polynomialTernaryQuaternionResiduesTrivialFor_laurentInfinity hfinite hno)
    hno

/--
The normalized-ordering quaternion criterion supplies the polynomial Legendre
construction after the rational-function isotropic solution is cleared back to
polynomials.
-/
theorem polynomialLegendreConstruction_of_normalizedOrderingRealization
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, u} R) :
    RatFunc.PolynomialLegendreConstruction R := by
  intro A B C hA0 hB0 hC0 hAsq hBsq hCsq hAB hAC hBC hfinite hno
  have hcriterion :
      PolynomialTernaryQuaternionSplitCriterion (R := R) :=
    polynomialTernaryQuaternionSplitCriterion_of_normalizedOrderingRealization
      hrealization
  have hiso :
      Diagonal.TernaryIsotropic
        (algebraMap (Polynomial R) (RatFunc R) A)
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C) :=
    polynomial_sqfree_pairwise_isotropic_of_polyQuaternionCriterion_laurentInfinity
      hcriterion hA0 hB0 hC0 hAsq hBsq hCsq hAB hAC hBC hfinite hno
  rcases
      (RatFunc.ternary_isotropic_iff_exists_polynomial_solution (R := R)
        (a₀ := algebraMap (Polynomial R) (RatFunc R) A)
        (a₁ := algebraMap (Polynomial R) (RatFunc R) B)
        (a₂ := algebraMap (Polynomial R) (RatFunc R) C)).mp hiso with
    ⟨x, y, z, hxyz, hsum⟩
  refine ⟨x, y, z, hxyz, ?_⟩
  apply _root_.RatFunc.algebraMap_injective R
  simpa [map_add, map_mul, map_pow] using hsum

end RatFuncWittLocalGlobal
