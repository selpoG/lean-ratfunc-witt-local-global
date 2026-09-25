/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Polynomial.NonlinearIrreducible.StandardComplexification
import RatFuncWittLocalGlobal.Polynomial.Positivity

/-!
# Signs of irreducible factors over a real closed field

This module is the sole bridge from the algebraic classification of
irreducible polynomials over a real closed field to the elementary interval
sign API.  The downstream `GapSign` module therefore depends on the
classification through a named mathematical boundary rather than through the
standard-complexification implementation.
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u

noncomputable section

/-- A normalized irreducible factor takes values with positive product at the
endpoints of a root-free interval. -/
theorem normalizedFactor_eval_mul_eval_pos_of_polynomial_ne_zero_on_Icc
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R]
    {p π : R[X]} {x y : R} (hxy : x ≤ y)
    (hπ : π ∈ UniqueFactorizationMonoid.normalizedFactors p)
    (hzero : ∀ z ∈ Set.Icc x y, p.eval z ≠ 0) :
    0 < π.eval x * π.eval y := by
  have hπirr : Irreducible π :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor π hπ
  have hπmonic : π.Monic := monic_of_mem_normalizedFactors hπ
  by_cases hdeg : π.natDegree = 1
  · obtain ⟨r, rfl⟩ :=
      exists_eq_X_sub_C_of_irreducible_monic_of_natDegree_eq_one
        hπirr hπmonic hdeg
    have hrnot : r ∉ Set.Icc x y := by
      intro hr
      apply hzero r hr
      exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
        (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hπ) (by simp)
    by_cases hxr : x ≤ r
    · have hry : y < r :=
        lt_of_not_ge (fun hry => hrnot ⟨hxr, hry⟩)
      have hxx : x - r < 0 := sub_neg.mpr (hxy.trans_lt hry)
      have hyy : y - r < 0 := sub_neg.mpr hry
      simpa using mul_pos_of_neg_of_neg hxx hyy
    · have hrx : r < x := lt_of_not_ge hxr
      have hxx : 0 < x - r := sub_pos.mpr hrx
      have hyy : 0 < y - r := sub_pos.mpr (hrx.trans_le hxy)
      simpa using mul_pos hxx hyy
  · have hdeg_le : π.natDegree ≤ 2 :=
      RatFunc.irreducibleNatDegreeLeTwo_of_realClosed π hπirr
    have hdeg_two : π.natDegree = 2 := by
      have hdeg_pos : 0 < π.natDegree :=
        Polynomial.natDegree_pos_iff_degree_pos.mpr
          (Polynomial.degree_pos_of_irreducible hπirr)
      omega
    have hnonneg : RatFunc.PolynomialEverywhereNonnegative π :=
      RatFunc.polynomialEverywhereNonnegative_of_standardFactorization
        (RatFunc.nonnegativePolynomialStandardFactorization_irreducible_monic_natDegree_two
          hπirr hπmonic hdeg_two)
    have hxne : π.eval x ≠ 0 :=
      eval_ne_zero_of_irreducible_of_natDegree_ne_one hπirr hdeg x
    have hyne : π.eval y ≠ 0 :=
      eval_ne_zero_of_irreducible_of_natDegree_ne_one hπirr hdeg y
    exact mul_pos (lt_of_le_of_ne (hnonneg x) (Ne.symm hxne))
      (lt_of_le_of_ne (hnonneg y) (Ne.symm hyne))

end

end RatFuncWittLocalGlobal
