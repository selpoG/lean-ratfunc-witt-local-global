/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.FiniteDimensional.Induction

/-!
# Public finite-dimensional local-global endpoints

This module removes the regularity hypothesis from the diagonal theorem and
provides universe-parameterized variants under explicit real-closure inputs.
-/

namespace RatFuncWittLocalGlobal

universe u v w

noncomputable section

/-- Total ordering criterion in dimension at least three.  A zero coefficient
already gives an isotropic coordinate vector; the regular branch is the
completed finite-dimensional theorem. -/
theorem diagonal_isotropic_iff_not_finiteSameStrictSignOrdering_of_card_ge_three_total
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] {ι : Type w} [Fintype ι]
    (hcard : 3 ≤ Fintype.card ι)
    (a : ι → _root_.RatFunc R) :
    Diagonal.Isotropic a ↔
      ¬ RatFunc.FiniteSameStrictSignOrdering a := by
  constructor
  · exact RatFunc.not_finiteSameStrictSignOrdering_of_isotropic a
  · intro hno
    by_cases ha : ∀ i, a i ≠ 0
    · exact diagonal_isotropic_of_not_finiteSameStrictSignOrdering_of_card_ge_three
        hcard a ha hno
    · simp only [not_forall, not_not] at ha
      rcases ha with ⟨i, hi⟩
      exact Diagonal.isotropic_of_zero_coeff a hi

/-- Total same-universe local-global principle in every finite dimension at
least three. -/
theorem diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_same_universe_total
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] {ι : Type w} [Fintype ι]
    (hcard : 3 ≤ Fintype.card ι)
    (a : ι → _root_.RatFunc R) :
    Diagonal.Isotropic a ↔
      ∀ {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
        [IsRealClosed K] [Algebra (_root_.RatFunc R) K],
        Diagonal.Isotropic (fun i =>
          algebraMap (_root_.RatFunc R) K (a i)) := by
  let _ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  constructor
  · intro hiso K _ _ _ _ _
    exact Diagonal.isotropic_baseChange hiso
  · intro hlocal
    have hno : ¬ RatFunc.FiniteSameStrictSignOrdering a :=
      RatFunc.not_finiteSameStrictSignOrdering_of_forall_realClosedExtension
        OrderedRealClosure.orderedFieldRealClosedExtension_same_universe a hlocal
    exact
      (diagonal_isotropic_iff_not_finiteSameStrictSignOrdering_of_card_ge_three_total
        hcard a).mpr hno

/-- Universe-parameterized total local-global theorem under the precise
real-closure input for ordered structures on `RatFunc R`. -/
theorem diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_of_ratFuncClosure
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] {ι : Type w} [Fintype ι]
    (hclosure : RatFunc.RatFuncOrderedRealClosedExtension.{u, v} R)
    (hcard : 3 ≤ Fintype.card ι)
    (a : ι → _root_.RatFunc R) :
    Diagonal.Isotropic a ↔
      ∀ {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
        [IsRealClosed K] [Algebra (_root_.RatFunc R) K],
        Diagonal.Isotropic (fun i =>
          algebraMap (_root_.RatFunc R) K (a i)) := by
  constructor
  · intro hiso K _ _ _ _ _
    exact Diagonal.isotropic_baseChange hiso
  · intro hlocal
    have hno : ¬ RatFunc.FiniteSameStrictSignOrdering a :=
      RatFunc.not_finiteSameStrictSignOrdering_of_forall_realClosedExtension_ratFuncClosure
        hclosure a hlocal
    exact
      (diagonal_isotropic_iff_not_finiteSameStrictSignOrdering_of_card_ge_three_total
        hcard a).mpr hno

/-- Universe-parameterized total local-global theorem under a real-closure
input for every ordered field in the base universe. -/
theorem diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_of_orderedFieldClosure
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] {ι : Type w} [Fintype ι]
    (hclosure : RatFunc.OrderedFieldRealClosedExtension.{u, v})
    (hcard : 3 ≤ Fintype.card ι)
    (a : ι → _root_.RatFunc R) :
    Diagonal.Isotropic a ↔
      ∀ {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
        [IsRealClosed K] [Algebra (_root_.RatFunc R) K],
        Diagonal.Isotropic (fun i =>
          algebraMap (_root_.RatFunc R) K (a i)) := by
  constructor
  · intro hiso K _ _ _ _ _
    exact Diagonal.isotropic_baseChange hiso
  · intro hlocal
    have hno : ¬ RatFunc.FiniteSameStrictSignOrdering a :=
      RatFunc.not_finiteSameStrictSignOrdering_of_forall_realClosedExtension
        hclosure a hlocal
    exact
      (diagonal_isotropic_iff_not_finiteSameStrictSignOrdering_of_card_ge_three_total
        hcard a).mpr hno

end

end RatFuncWittLocalGlobal
