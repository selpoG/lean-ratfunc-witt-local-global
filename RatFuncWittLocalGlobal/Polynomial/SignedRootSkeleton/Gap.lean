/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Polynomial.SignedRootSkeleton.Basic
import RatFuncWittLocalGlobal.Polynomial.LocalLaurent
import RatFuncWittLocalGlobal.Polynomial.GapSign
import RatFuncWittLocalGlobal.Sign.Strict

/-!
# Signed linear-root skeletons across root-free gaps

Dimension-independent sign lemmas for a squarefree product of distinct linear
factors.  They compare ordinary evaluations with Laurent leading coefficients
at the endpoints of root-free intervals.
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u v

noncomputable section

/-- The right Laurent sign of a skeleton at the left endpoint equals its
ordinary sign at the right endpoint when the intervening half-gap has no
skeleton root. -/
theorem SignedLinearRootSkeleton.localLaurentLeadingCoeff_one_pos_iff_eval_pos_of_gap
    {R : Type u} [Field R] [CharZero R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R]
    (S : SignedLinearRootSkeleton R) {r s : R} (hrs : r < s)
    (hgap : ∀ z ∈ Set.Ioc r s, z ∉ S.roots) :
    0 < localLaurentLeadingCoeff r 1 S.poly ↔
      0 < S.poly.eval s := by
  by_cases hroot : S.poly.eval r = 0
  · have hroot' : S.poly.IsRoot r := by simpa [Polynomial.IsRoot] using hroot
    let q := S.poly /ₘ (X - C r)
    have hqne : q.eval r ≠ 0 :=
      eval_divByMonic_X_sub_C_ne_zero_of_squarefree_of_isRoot S.poly_squarefree hroot'
    have hp_factor : (X - C r) * q = S.poly :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot'
    have hlead :
        localLaurentLeadingCoeff r 1 S.poly = q.eval r := by
      rw [← hp_factor, localLaurentLeadingCoeff_mul,
        localLaurentLeadingCoeff_X_sub_C,
        localLaurentLeadingCoeff_eq_eval_of_ne_zero hqne]
      simp
    rw [hlead]
    exact polynomial_divByMonic_eval_pos_iff_eval_pos_of_squarefree_of_isRoot_of_ne_zero_on_Ioc
      S.poly_squarefree hroot' hrs (fun z hz => by
        intro hz0
        exact hgap z hz ((S.eval_poly_eq_zero_iff z).mp hz0))
  · rw [localLaurentLeadingCoeff_eq_eval_of_ne_zero hroot]
    apply polynomial_eval_pos_iff_of_ne_zero_on_Icc hrs.le
    intro z hz
    by_cases hzr : z = r
    · simpa [hzr] using hroot
    · intro hz0
      exact hgap z ⟨lt_of_le_of_ne hz.1 (Ne.symm hzr), hz.2⟩
        ((S.eval_poly_eq_zero_iff z).mp hz0)

/-- The ordinary sign at the left endpoint equals the left Laurent sign at
the right endpoint when the intervening half-gap has no skeleton root. -/
theorem SignedLinearRootSkeleton.eval_pos_iff_localLaurentLeadingCoeff_neg_one_of_gap
    {R : Type u} [Field R] [CharZero R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R]
    (S : SignedLinearRootSkeleton R) {r s : R} (hrs : r < s)
    (hgap : ∀ z ∈ Set.Ico r s, z ∉ S.roots) :
    0 < S.poly.eval r ↔
      0 < localLaurentLeadingCoeff s (-1) S.poly := by
  by_cases hroot : S.poly.eval s = 0
  · have hroot' : S.poly.IsRoot s := by simpa [Polynomial.IsRoot] using hroot
    let q := S.poly /ₘ (X - C s)
    have hqne : q.eval s ≠ 0 :=
      eval_divByMonic_X_sub_C_ne_zero_of_squarefree_of_isRoot S.poly_squarefree hroot'
    have hp_factor : (X - C s) * q = S.poly :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot'
    have hlead :
        localLaurentLeadingCoeff s (-1) S.poly = -q.eval s := by
      rw [← hp_factor, localLaurentLeadingCoeff_mul,
        localLaurentLeadingCoeff_X_sub_C,
        localLaurentLeadingCoeff_eq_eval_of_ne_zero hqne]
      ring
    rw [hlead]
    exact polynomial_eval_pos_iff_neg_divByMonic_eval_of_squarefree_of_isRoot_of_ne_zero_on_Ico
      S.poly_squarefree hroot' hrs (fun z hz => by
        intro hz0
        exact hgap z hz ((S.eval_poly_eq_zero_iff z).mp hz0))
  · rw [localLaurentLeadingCoeff_eq_eval_of_ne_zero hroot]
    apply polynomial_eval_pos_iff_of_ne_zero_on_Icc hrs.le
    intro z hz
    by_cases hzs : z = s
    · simpa [hzs] using hroot
    · intro hz0
      exact hgap z ⟨hz.1, lt_of_le_of_ne hz.2 hzs⟩
        ((S.eval_poly_eq_zero_iff z).mp hz0)

/-- A root-free open gap preserves the two inward Laurent signs of a signed
skeleton. -/
theorem SignedLinearRootSkeleton.localLaurentLeadingCoeff_pos_iff_across_gap
    {R : Type u} [Field R] [CharZero R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R]
    (S : SignedLinearRootSkeleton R) {r s : R} (hrs : r < s)
    (hgap : ∀ z, r < z → z < s → z ∉ S.roots) :
    0 < localLaurentLeadingCoeff r 1 S.poly ↔
      0 < localLaurentLeadingCoeff s (-1) S.poly := by
  let t := (r + s) / 2
  have hrt : r < t := by dsimp [t]; linarith
  have hts : t < s := by dsimp [t]; linarith
  exact
    (S.localLaurentLeadingCoeff_one_pos_iff_eval_pos_of_gap hrt
      (fun z hz => hgap z hz.1 (hz.2.trans_lt hts))).trans
    (S.eval_pos_iff_localLaurentLeadingCoeff_neg_one_of_gap hts
      (fun z hz => hgap z (hrt.trans_le hz.1) hz.2))

/-- Every nontrivially oriented local Laurent leading coefficient of a signed
skeleton is nonzero. -/
theorem SignedLinearRootSkeleton.localLaurentLeadingCoeff_ne_zero
    {R : Type u} [Field R] [CharZero R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (S : SignedLinearRootSkeleton R) (r ε : R) (hε : ε ≠ 0) :
    localLaurentLeadingCoeff r ε S.poly ≠ 0 := by
  by_cases hr : r ∈ S.roots
  · rw [localLaurentLeadingCoeff,
      S.poly_eq_X_sub_C_mul_cofactorAt hr,
      RatFunc.scaledShifted_X_sub_C_mul_polynomial_laurentSeries_leadingCoeff
        (S.eval_cofactorAt_ne_zero r)]
    exact mul_ne_zero (S.eval_cofactorAt_ne_zero r) hε
  · have heval : S.poly.eval r ≠ 0 := by
      intro hz
      exact hr ((S.eval_poly_eq_zero_iff r).mp hz)
    rw [localLaurentLeadingCoeff_eq_eval_of_ne_zero heval]
    exact heval

/-- Equality of positivity for two nonzero values transports every strict
sign. -/
theorem StrictSign.holds_iff_of_pos_iff
    {R : Type u} {S : Type v}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Field S] [LinearOrder S] [IsStrictOrderedRing S]
    (sign : StrictSign) {x : R} {y : S} (hx : x ≠ 0) (hy : y ≠ 0)
    (hpos : 0 < x ↔ 0 < y) :
    sign.Holds x ↔ sign.Holds y := by
  cases sign with
  | pos => exact hpos
  | neg =>
      constructor
      · intro hxneg
        have hnot : ¬0 < y := fun hypos =>
          (not_lt_of_ge hxneg.le) (hpos.mpr hypos)
        exact lt_of_le_of_ne (le_of_not_gt hnot) hy
      · intro hyneg
        have hnot : ¬0 < x := fun hxpos =>
          (not_lt_of_ge hyneg.le) (hpos.mp hxpos)
        exact lt_of_le_of_ne (le_of_not_gt hnot) hx

/-- A root-free open gap preserves every strict sign between the two inward
Laurent sides of a signed skeleton. -/
theorem SignedLinearRootSkeleton.localLaurentLeadingCoeff_holds_iff_across_gap
    {R : Type u} [Field R] [CharZero R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R]
    (S : SignedLinearRootSkeleton R) (sign : StrictSign)
    {r s : R} (hrs : r < s)
    (hgap : ∀ z, r < z → z < s → z ∉ S.roots) :
    sign.Holds (localLaurentLeadingCoeff r 1 S.poly) ↔
      sign.Holds
        (localLaurentLeadingCoeff s (-1) S.poly) := by
  apply sign.holds_iff_of_pos_iff
    (S.localLaurentLeadingCoeff_ne_zero r 1 one_ne_zero)
    (S.localLaurentLeadingCoeff_ne_zero s (-1) (by simp))
  exact S.localLaurentLeadingCoeff_pos_iff_across_gap hrs hgap

/-- At a recorded simple root, changing Laurent orientation from right to
left negates the leading coefficient. -/
theorem SignedLinearRootSkeleton.localLaurentLeadingCoeff_neg_one_eq_neg_one
    {R : Type u} [Field R] [CharZero R]
    (S : SignedLinearRootSkeleton R) {r : R} (hr : r ∈ S.roots) :
    localLaurentLeadingCoeff r (-1) S.poly =
      -localLaurentLeadingCoeff r 1 S.poly := by
  have hleft : localLaurentLeadingCoeff r (-1) S.poly =
      (S.cofactorAt r).eval r * (-1) := by
    rw [localLaurentLeadingCoeff,
      S.poly_eq_X_sub_C_mul_cofactorAt hr]
    exact RatFunc.scaledShifted_X_sub_C_mul_polynomial_laurentSeries_leadingCoeff
      (S.eval_cofactorAt_ne_zero r)
  have hright : localLaurentLeadingCoeff r 1 S.poly =
      (S.cofactorAt r).eval r * 1 := by
    rw [localLaurentLeadingCoeff,
      S.poly_eq_X_sub_C_mul_cofactorAt hr]
    exact RatFunc.scaledShifted_X_sub_C_mul_polynomial_laurentSeries_leadingCoeff
      (S.eval_cofactorAt_ne_zero r)
  rw [hleft, hright]
  ring

end
end RatFuncWittLocalGlobal
