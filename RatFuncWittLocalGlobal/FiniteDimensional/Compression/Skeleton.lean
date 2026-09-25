/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.FiniteDimensional.PolynomialState
import RatFuncWittLocalGlobal.FiniteDimensional.Compression.Sign
import RatFuncWittLocalGlobal.Polynomial.SignedRootSkeleton.Gap
import RatFuncWittLocalGlobal.Polynomial.SignedRootSkeleton.Rescale
import RatFuncWittLocalGlobal.Sign.Propagation

/-!
# Ordinary sign skeleton for binary-tail compression

The coefficients are indexed by a binary head plus an arbitrary finite tail.
The skeleton records exactly the real roots at which the required compression
sign changes.
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u w

noncomputable section

namespace FinitePolynomialState

variable {R : Type u} {κ : Type w} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Fintype κ]
  {a : Sum (Fin 2) κ → _root_.RatFunc R}

/-- Laurent-side scalar coefficients of a finite polynomial state. -/
def localCoefficientFamily (T : FinitePolynomialState a)
    (r ε : R) : Sum (Fin 2) κ → R :=
  fun i => localLaurentLeadingCoeff r ε (T.A i)

theorem localCoefficientFamily_ne_zero (T : FinitePolynomialState a)
    (i : Sum (Fin 2) κ) (r ε : R) (hε : ε ≠ 0) :
    T.localCoefficientFamily r ε i ≠ 0 := by
  let p := T.A i
  by_cases hroot : p.eval r = 0
  · have hroot' : p.IsRoot r := by simpa [Polynomial.IsRoot] using hroot
    let q := p /ₘ (X - C r)
    have hqne : q.eval r ≠ 0 :=
      eval_divByMonic_X_sub_C_ne_zero_of_squarefree_of_isRoot
        (T.normal_form i).2.2.1 hroot'
    have hp_factor : (X - C r) * q = p :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot'
    change localLaurentLeadingCoeff r ε p ≠ 0
    rw [← hp_factor, localLaurentLeadingCoeff_mul,
      localLaurentLeadingCoeff_X_sub_C,
      localLaurentLeadingCoeff_eq_eval_of_ne_zero hqne]
    exact mul_ne_zero hε hqne
  · rw [localCoefficientFamily,
      localLaurentLeadingCoeff_eq_eval_of_ne_zero hroot]
    exact hroot

theorem coefficient_eval_pos_iff_of_rootFree_Icc
    [IsRealClosed R] (T : FinitePolynomialState a)
    {x y : R} (hxy : x ≤ y)
    (hgap : ∀ z ∈ Set.Icc x y, z ∉ T.realRoots)
    (i : Sum (Fin 2) κ) :
    0 < (T.A i).eval x ↔ 0 < (T.A i).eval y := by
  apply polynomial_eval_pos_iff_of_ne_zero_on_Icc hxy
  intro z hz
  exact T.eval_ne_zero_of_not_mem_realRoots (hgap z hz) i

theorem localCoefficient_one_pos_iff_eval_of_gap
    [IsRealClosed R] (T : FinitePolynomialState a)
    (i : Sum (Fin 2) κ) {r s : R} (hrs : r < s)
    (hgap : ∀ z ∈ Set.Ioc r s, z ∉ T.realRoots) :
    0 < T.localCoefficientFamily r 1 i ↔ 0 < (T.A i).eval s := by
  let p := T.A i
  by_cases hroot : p.eval r = 0
  · have hroot' : p.IsRoot r := by simpa [Polynomial.IsRoot] using hroot
    let q := p /ₘ (X - C r)
    have hqne : q.eval r ≠ 0 :=
      eval_divByMonic_X_sub_C_ne_zero_of_squarefree_of_isRoot
        (T.normal_form i).2.2.1 hroot'
    have hp_factor : (X - C r) * q = p :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot'
    have hlead : T.localCoefficientFamily r 1 i = q.eval r := by
      change localLaurentLeadingCoeff r 1 p = q.eval r
      rw [← hp_factor, localLaurentLeadingCoeff_mul,
        localLaurentLeadingCoeff_X_sub_C,
        localLaurentLeadingCoeff_eq_eval_of_ne_zero hqne]
      simp
    rw [hlead]
    simpa [p, q] using
      polynomial_divByMonic_eval_pos_iff_eval_pos_of_squarefree_of_isRoot_of_ne_zero_on_Ioc
        (T.normal_form i).2.2.1 hroot' hrs
          (fun z hz => T.eval_ne_zero_of_not_mem_realRoots (hgap z hz) i)
  · rw [localCoefficientFamily,
      localLaurentLeadingCoeff_eq_eval_of_ne_zero hroot]
    apply polynomial_eval_pos_iff_of_ne_zero_on_Icc hrs.le
    intro z hz
    by_cases hzr : z = r
    · simpa [p, hzr] using hroot
    · exact T.eval_ne_zero_of_not_mem_realRoots
        (hgap z ⟨lt_of_le_of_ne hz.1 (Ne.symm hzr), hz.2⟩) i

theorem eval_pos_iff_localCoefficient_neg_one_of_gap
    [IsRealClosed R] (T : FinitePolynomialState a)
    (i : Sum (Fin 2) κ) {r s : R} (hrs : r < s)
    (hgap : ∀ z ∈ Set.Ico r s, z ∉ T.realRoots) :
    0 < (T.A i).eval r ↔ 0 < T.localCoefficientFamily s (-1) i := by
  let p := T.A i
  by_cases hroot : p.eval s = 0
  · have hroot' : p.IsRoot s := by simpa [Polynomial.IsRoot] using hroot
    let q := p /ₘ (X - C s)
    have hqne : q.eval s ≠ 0 :=
      eval_divByMonic_X_sub_C_ne_zero_of_squarefree_of_isRoot
        (T.normal_form i).2.2.1 hroot'
    have hp_factor : (X - C s) * q = p :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot'
    have hlead : T.localCoefficientFamily s (-1) i = -q.eval s := by
      change localLaurentLeadingCoeff s (-1) p = -q.eval s
      rw [← hp_factor, localLaurentLeadingCoeff_mul,
        localLaurentLeadingCoeff_X_sub_C,
        localLaurentLeadingCoeff_eq_eval_of_ne_zero hqne]
      ring
    rw [hlead]
    simpa [p, q] using
      polynomial_eval_pos_iff_neg_divByMonic_eval_of_squarefree_of_isRoot_of_ne_zero_on_Ico
        (T.normal_form i).2.2.1 hroot' hrs
          (fun z hz => T.eval_ne_zero_of_not_mem_realRoots (hgap z hz) i)
  · rw [localCoefficientFamily,
      localLaurentLeadingCoeff_eq_eval_of_ne_zero hroot]
    apply polynomial_eval_pos_iff_of_ne_zero_on_Icc hrs.le
    intro z hz
    by_cases hzs : z = s
    · simpa [p, hzs] using hroot
    · exact T.eval_ne_zero_of_not_mem_realRoots
        (hgap z ⟨hz.1, lt_of_le_of_ne hz.2 hzs⟩) i

/-- Required binary-tail compression sign on a Laurent side. -/
def binaryTailSign (T : FinitePolynomialState a) (r ε : R) : StrictSign :=
  binaryTailCompressionRequiredSign
    (fun i => T.localCoefficientFamily r ε (Sum.inl i))
    (fun j => T.localCoefficientFamily r ε (Sum.inr j))

theorem binaryTailSign_eq_across_gap [IsRealClosed R]
    (T : FinitePolynomialState a) {r s : R} (hrs : r < s)
    (hgap : ∀ z, r < z → z < s → z ∉ T.realRoots) :
    T.binaryTailSign r 1 = T.binaryTailSign s (-1) := by
  let y := (r + s) / 2
  have hry : r < y := by dsimp [y]; linarith
  have hys : y < s := by dsimp [y]; linarith
  let B : Sum (Fin 2) κ → R := fun i => (T.A i).eval y
  have hB (i : Sum (Fin 2) κ) : B i ≠ 0 :=
    T.eval_ne_zero_of_not_mem_realRoots (hgap y hry hys) i
  calc
    T.binaryTailSign r 1 =
        binaryTailCompressionRequiredSign
          (fun i => B (Sum.inl i)) (fun j => B (Sum.inr j)) := by
      apply binaryTailCompressionRequiredSign_eq_of_pos_iff
      · exact fun j => T.localCoefficientFamily_ne_zero (Sum.inr j) r 1 one_ne_zero
      · exact fun j => hB (Sum.inr j)
      · intro i
        exact T.localCoefficient_one_pos_iff_eval_of_gap (Sum.inl i) hry
          (fun z hz => hgap z hz.1 (hz.2.trans_lt hys))
      · intro j
        exact T.localCoefficient_one_pos_iff_eval_of_gap (Sum.inr j) hry
          (fun z hz => hgap z hz.1 (hz.2.trans_lt hys))
    _ = T.binaryTailSign s (-1) := by
      apply binaryTailCompressionRequiredSign_eq_of_pos_iff
      · exact fun j => hB (Sum.inr j)
      · exact fun j => T.localCoefficientFamily_ne_zero (Sum.inr j) s (-1) (by norm_num)
      · intro i
        exact T.eval_pos_iff_localCoefficient_neg_one_of_gap (Sum.inl i) hys
          (fun z hz => hgap z (hry.trans_le hz.1) hz.2)
      · intro j
        exact T.eval_pos_iff_localCoefficient_neg_one_of_gap (Sum.inr j) hys
          (fun z hz => hgap z (hry.trans_le hz.1) hz.2)

def binaryTailRightSign (T : FinitePolynomialState a) (r : R) : StrictSign :=
  T.binaryTailSign r 1

def binaryTailLeftSign (T : FinitePolynomialState a) (r : R) : StrictSign :=
  T.binaryTailSign r (-1)

noncomputable def binaryTailOddRoots (T : FinitePolynomialState a) : Finset R := by
  classical
  exact T.realRoots.filter fun r =>
    T.binaryTailLeftSign r ≠ T.binaryTailRightSign r

omit [IsStrictOrderedRing R] in
theorem mem_binaryTailOddRoots_iff (T : FinitePolynomialState a) (r : R) :
    r ∈ T.binaryTailOddRoots ↔
      r ∈ T.realRoots ∧
        T.binaryTailLeftSign r ≠ T.binaryTailRightSign r := by
  classical
  simp [binaryTailOddRoots]

omit [IsStrictOrderedRing R] in
theorem binaryTailOddRoots_subset_realRoots (T : FinitePolynomialState a) :
    T.binaryTailOddRoots ⊆ T.realRoots := by
  intro r hr
  exact (T.mem_binaryTailOddRoots_iff r).mp hr |>.1

def binaryTailSkeleton (T : FinitePolynomialState a)
    (scale : R) (hscale : scale ≠ 0) : SignedLinearRootSkeleton R where
  roots := T.binaryTailOddRoots
  scale := scale
  scale_ne_zero := hscale

theorem binaryTailEndpointRequirements_iff
    (T : FinitePolynomialState a) (r scale : R) (hscale : scale ≠ 0) :
    let S := T.binaryTailSkeleton scale hscale
    (T.binaryTailRightSign r).Holds
        (localLaurentLeadingCoeff r 1 S.poly) ↔
      (T.binaryTailLeftSign r).Holds
        (localLaurentLeadingCoeff r (-1) S.poly) := by
  let S := T.binaryTailSkeleton scale hscale
  by_cases hne : T.binaryTailLeftSign r ≠ T.binaryTailRightSign r
  · have hr : r ∈ T.realRoots := by
      by_contra hr
      apply hne
      apply binaryTailCompressionRequiredSign_eq_of_pos_iff
      · exact fun j => T.localCoefficientFamily_ne_zero (Sum.inr j) r (-1) (by norm_num)
      · exact fun j => T.localCoefficientFamily_ne_zero (Sum.inr j) r 1 one_ne_zero
      · intro i
        have hi := T.eval_ne_zero_of_not_mem_realRoots hr (Sum.inl i)
        change 0 < localLaurentLeadingCoeff r (-1) (T.A (Sum.inl i)) ↔
          0 < localLaurentLeadingCoeff r 1 (T.A (Sum.inl i))
        rw [localLaurentLeadingCoeff_eq_eval_of_ne_zero hi,
          localLaurentLeadingCoeff_eq_eval_of_ne_zero hi]
      · intro j
        have hj := T.eval_ne_zero_of_not_mem_realRoots hr (Sum.inr j)
        change 0 < localLaurentLeadingCoeff r (-1) (T.A (Sum.inr j)) ↔
          0 < localLaurentLeadingCoeff r 1 (T.A (Sum.inr j))
        rw [localLaurentLeadingCoeff_eq_eval_of_ne_zero hj,
          localLaurentLeadingCoeff_eq_eval_of_ne_zero hj]
    have hroot : r ∈ S.roots :=
      (T.mem_binaryTailOddRoots_iff r).mpr ⟨hr, hne⟩
    have hop : (T.binaryTailLeftSign r).opposite = T.binaryTailRightSign r :=
      StrictSign.opposite_eq_of_ne _ _ hne
    change (T.binaryTailRightSign r).Holds
        (localLaurentLeadingCoeff r 1 S.poly) ↔
      (T.binaryTailLeftSign r).Holds
        (localLaurentLeadingCoeff r (-1) S.poly)
    rw [S.localLaurentLeadingCoeff_neg_one_eq_neg_one hroot, ← hop]
    cases T.binaryTailLeftSign r <;>
      simp [StrictSign.Holds, StrictSign.opposite]
  · have heq : T.binaryTailLeftSign r = T.binaryTailRightSign r :=
      not_ne_iff.mp hne
    have hnot : r ∉ S.roots := by
      intro hroot
      exact hne ((T.mem_binaryTailOddRoots_iff r).mp hroot).2
    have heval : S.poly.eval r ≠ 0 := by
      intro hz
      exact hnot ((S.eval_poly_eq_zero_iff r).mp hz)
    change (T.binaryTailRightSign r).Holds
        (localLaurentLeadingCoeff r 1 S.poly) ↔
      (T.binaryTailLeftSign r).Holds
        (localLaurentLeadingCoeff r (-1) S.poly)
    rw [localLaurentLeadingCoeff_eq_eval_of_ne_zero heval,
      localLaurentLeadingCoeff_eq_eval_of_ne_zero heval, heq]

theorem binaryTailRightRequirements_iff_across_gap [IsRealClosed R]
    (T : FinitePolynomialState a) {r s : R} (hrs : r < s)
    (hgap : ∀ z ∈ T.realRoots, ¬ (r < z ∧ z < s))
    (scale : R) (hscale : scale ≠ 0) :
    let S := T.binaryTailSkeleton scale hscale
    (T.binaryTailRightSign r).Holds
        (localLaurentLeadingCoeff r 1 S.poly) ↔
      (T.binaryTailRightSign s).Holds
        (localLaurentLeadingCoeff s 1 S.poly) := by
  let S := T.binaryTailSkeleton scale hscale
  have hnoRoot : ∀ z, r < z → z < s → z ∉ S.roots := by
    intro z hrz hzs hz
    exact hgap z (T.binaryTailOddRoots_subset_realRoots hz) ⟨hrz, hzs⟩
  have hsign : T.binaryTailRightSign r = T.binaryTailLeftSign s :=
    T.binaryTailSign_eq_across_gap hrs
      (fun z hrz hzs hz => hgap z hz ⟨hrz, hzs⟩)
  have hinward := S.localLaurentLeadingCoeff_holds_iff_across_gap
    (T.binaryTailRightSign r) hrs hnoRoot
  exact hinward.trans (by
    rw [hsign]
    exact (T.binaryTailEndpointRequirements_iff s scale hscale).symm)

theorem exists_binaryTailScale_at (T : FinitePolynomialState a) (r : R) :
    ∃ (scale : R) (hscale : scale ≠ 0),
      (scale = 1 ∨ scale = -1) ∧
      (T.binaryTailRightSign r).Holds
        (localLaurentLeadingCoeff r 1
          (T.binaryTailSkeleton scale hscale).poly) := by
  let S := T.binaryTailSkeleton 1 one_ne_zero
  let sign := T.binaryTailRightSign r
  let x := localLaurentLeadingCoeff r 1 S.poly
  have hx : x ≠ 0 := S.localLaurentLeadingCoeff_ne_zero _ 1 one_ne_zero
  rcases sign.holds_or_holds_neg hx with hpos | hneg
  · exact ⟨1, one_ne_zero, Or.inl rfl, by simpa [S, sign, x] using hpos⟩
  · refine ⟨-1, by simp, Or.inr rfl, ?_⟩
    have hrescale : T.binaryTailSkeleton (-1) (by simp) =
        S.rescale (-1) (by simp) := by
      apply SignedLinearRootSkeleton.ext
      · rfl
      · simp [S, binaryTailSkeleton, SignedLinearRootSkeleton.rescale]
    rw [hrescale, SignedLinearRootSkeleton.localLaurentLeadingCoeff_rescale]
    simpa [sign, x] using hneg

theorem exists_binaryTailSkeleton_endpoints [IsRealClosed R]
    (T : FinitePolynomialState a) (hroots : T.realRoots.Nonempty) :
    ∃ (scale : R) (hscale : scale ≠ 0),
      (scale = 1 ∨ scale = -1) ∧
      ∀ r ∈ T.realRoots,
        (T.binaryTailRightSign r).Holds
            (localLaurentLeadingCoeff r 1
              (T.binaryTailSkeleton scale hscale).poly) ∧
          (T.binaryTailLeftSign r).Holds
            (localLaurentLeadingCoeff r (-1)
              (T.binaryTailSkeleton scale hscale).poly) := by
  classical
  let s : Finset R := T.realRoots
  have hs : s.Nonempty := hroots
  let r₀ : R := s.min' hs
  rcases T.exists_binaryTailScale_at r₀ with
    ⟨scale, hscale, hscaleSign, hr₀⟩
  let P : R → Prop := fun r =>
    (T.binaryTailRightSign r).Holds
      (localLaurentLeadingCoeff r 1
        (T.binaryTailSkeleton scale hscale).poly)
  have hstep : ∀ r ∈ s, ∀ t ∈ s, r < t →
      (∀ z ∈ s, ¬ (r < z ∧ z < t)) → (P r ↔ P t) := by
    intro r _ t _ hrt hbetween
    exact T.binaryTailRightRequirements_iff_across_gap hrt
      (fun z hz => hbetween z hz) scale hscale
  have hall : ∀ r ∈ s, P r :=
    Finset.forall_of_min'_of_consecutive_iff s P hstep hs hr₀
  refine ⟨scale, hscale, hscaleSign, fun r hr => ⟨?_, ?_⟩⟩
  · exact hall r hr
  · exact (T.binaryTailEndpointRequirements_iff r scale hscale).mp
      (hall r hr)

end FinitePolynomialState

end

end RatFuncWittLocalGlobal
