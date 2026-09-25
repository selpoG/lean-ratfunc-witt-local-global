/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.FiniteDimensional.Compression.Skeleton

/-!
# Ordinary real realization of binary-tail compression
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u w

noncomputable section

namespace FinitePolynomialState

variable {R : Type u} {κ : Type w} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R] [Fintype κ]
  {a : Sum (Fin 2) κ → _root_.RatFunc R}

theorem binaryTailSignHolds_eval_of_right_gap
    (T : FinitePolynomialState a) (S : SignedLinearRootSkeleton R)
    {r y : R} (hry : r < y)
    (hgap : ∀ z ∈ Set.Ioc r y, z ∉ T.realRoots)
    (hSroots : S.roots ⊆ T.realRoots)
    (hlocal : (T.binaryTailRightSign r).Holds
      (localLaurentLeadingCoeff r 1 S.poly)) :
    (binaryTailCompressionRequiredSign
      (fun i => (T.A (Sum.inl i)).eval y)
      (fun j => (T.A (Sum.inr j)).eval y)).Holds (S.poly.eval y) := by
  let B : Sum (Fin 2) κ → R := fun i => (T.A i).eval y
  have hB (i : Sum (Fin 2) κ) : B i ≠ 0 :=
    T.eval_ne_zero_of_not_mem_realRoots (hgap y ⟨hry, le_rfl⟩) i
  have hsign : T.binaryTailRightSign r =
      binaryTailCompressionRequiredSign
        (fun i => B (Sum.inl i)) (fun j => B (Sum.inr j)) := by
    apply binaryTailCompressionRequiredSign_eq_of_pos_iff
    · exact fun j => T.localCoefficientFamily_ne_zero (Sum.inr j) r 1 one_ne_zero
    · exact fun j => hB (Sum.inr j)
    · intro i
      exact T.localCoefficient_one_pos_iff_eval_of_gap (Sum.inl i) hry hgap
    · intro j
      exact T.localCoefficient_one_pos_iff_eval_of_gap (Sum.inr j) hry hgap
  have hlocal0 :
      localLaurentLeadingCoeff r 1 S.poly ≠ 0 :=
    S.localLaurentLeadingCoeff_ne_zero r 1 one_ne_zero
  have hSy : S.poly.eval y ≠ 0 := by
    intro hz
    exact hgap y ⟨hry, le_rfl⟩
      (hSroots ((S.eval_poly_eq_zero_iff y).mp hz))
  have hSpos :
      0 < localLaurentLeadingCoeff r 1 S.poly ↔
        0 < S.poly.eval y :=
    S.localLaurentLeadingCoeff_one_pos_iff_eval_pos_of_gap hry
      (fun z hz hroot => hgap z hz (hSroots hroot))
  rw [hsign] at hlocal
  exact (StrictSign.holds_iff_of_pos_iff _ hlocal0 hSy hSpos).mp hlocal

theorem binaryTailSignHolds_eval_of_left_gap
    (T : FinitePolynomialState a) (S : SignedLinearRootSkeleton R)
    {y r : R} (hyr : y < r)
    (hgap : ∀ z ∈ Set.Ico y r, z ∉ T.realRoots)
    (hSroots : S.roots ⊆ T.realRoots)
    (hlocal : (T.binaryTailLeftSign r).Holds
      (localLaurentLeadingCoeff r (-1) S.poly)) :
    (binaryTailCompressionRequiredSign
      (fun i => (T.A (Sum.inl i)).eval y)
      (fun j => (T.A (Sum.inr j)).eval y)).Holds (S.poly.eval y) := by
  let B : Sum (Fin 2) κ → R := fun i => (T.A i).eval y
  have hB (i : Sum (Fin 2) κ) : B i ≠ 0 :=
    T.eval_ne_zero_of_not_mem_realRoots (hgap y ⟨le_rfl, hyr⟩) i
  have hsign : binaryTailCompressionRequiredSign
      (fun i => B (Sum.inl i)) (fun j => B (Sum.inr j)) =
        T.binaryTailLeftSign r := by
    apply binaryTailCompressionRequiredSign_eq_of_pos_iff
    · exact fun j => hB (Sum.inr j)
    · exact fun j => T.localCoefficientFamily_ne_zero (Sum.inr j) r (-1) (by norm_num)
    · intro i
      exact T.eval_pos_iff_localCoefficient_neg_one_of_gap (Sum.inl i) hyr hgap
    · intro j
      exact T.eval_pos_iff_localCoefficient_neg_one_of_gap (Sum.inr j) hyr hgap
  have hlocal0 :
      localLaurentLeadingCoeff r (-1) S.poly ≠ 0 :=
    S.localLaurentLeadingCoeff_ne_zero r (-1) (by norm_num)
  have hSy : S.poly.eval y ≠ 0 := by
    intro hz
    exact hgap y ⟨le_rfl, hyr⟩
      (hSroots ((S.eval_poly_eq_zero_iff y).mp hz))
  have hSpos : 0 < S.poly.eval y ↔
      0 < localLaurentLeadingCoeff r (-1) S.poly :=
    S.eval_pos_iff_localLaurentLeadingCoeff_neg_one_of_gap hyr
      (fun z hz hroot => hgap z hz (hSroots hroot))
  rw [← hsign] at hlocal
  exact (StrictSign.holds_iff_of_pos_iff _ hSy hlocal0 hSpos).mpr hlocal

theorem binaryTailSignHolds_eval_of_endpoints
    (T : FinitePolynomialState a) (S : SignedLinearRootSkeleton R)
    (hSroots : S.roots ⊆ T.realRoots)
    (hendpoint : ∀ r ∈ T.realRoots,
      (T.binaryTailRightSign r).Holds
          (localLaurentLeadingCoeff r 1 S.poly) ∧
        (T.binaryTailLeftSign r).Holds
          (localLaurentLeadingCoeff r (-1) S.poly))
    {y : R} (hy : y ∉ T.realRoots) (hroots : T.realRoots.Nonempty) :
    (binaryTailCompressionRequiredSign
      (fun i => (T.A (Sum.inl i)).eval y)
      (fun j => (T.A (Sum.inr j)).eval y)).Holds (S.poly.eval y) := by
  classical
  let below := T.realRoots.filter (fun r => r < y)
  by_cases hbelow : below.Nonempty
  · let r := below.max' hbelow
    have hrBelow : r ∈ below := below.max'_mem hbelow
    have hr : r ∈ T.realRoots := (Finset.mem_filter.mp hrBelow).1
    have hry : r < y := (Finset.mem_filter.mp hrBelow).2
    have hgap : ∀ z ∈ Set.Ioc r y, z ∉ T.realRoots := by
      intro z hz hzroot
      have hzy : z < y := lt_of_le_of_ne hz.2 (fun h => hy (h ▸ hzroot))
      have hzBelow : z ∈ below := Finset.mem_filter.mpr ⟨hzroot, hzy⟩
      exact (not_lt_of_ge (below.le_max' z hzBelow)) hz.1
    exact T.binaryTailSignHolds_eval_of_right_gap S hry hgap hSroots
      (hendpoint r hr).1
  · let r := T.realRoots.min' hroots
    have hr : r ∈ T.realRoots := T.realRoots.min'_mem hroots
    have hyr : y < r := by
      have hnot : ¬ r < y := fun hry =>
        hbelow ⟨r, Finset.mem_filter.mpr ⟨hr, hry⟩⟩
      exact lt_of_le_of_ne (le_of_not_gt hnot) (fun h => hy (h.symm ▸ hr))
    have hgap : ∀ z ∈ Set.Ico y r, z ∉ T.realRoots := by
      intro z hz hzroot
      exact (not_lt_of_ge (T.realRoots.min'_le z hzroot)) hz.2
    exact T.binaryTailSignHolds_eval_of_left_gap S hyr hgap hSroots
      (hendpoint r hr).2

/-- A single signed skeleton realizes the binary-tail sign rule at every
ordinary point away from the coefficient roots. -/
theorem exists_binaryTailSkeleton_eval (T : FinitePolynomialState a) :
    ∃ S : SignedLinearRootSkeleton R,
      S.roots ⊆ T.realRoots ∧
      ∀ y, y ∉ T.realRoots →
        (binaryTailCompressionRequiredSign
          (fun i => (T.A (Sum.inl i)).eval y)
          (fun j => (T.A (Sum.inr j)).eval y)).Holds (S.poly.eval y) := by
  classical
  by_cases hroots : T.realRoots.Nonempty
  · rcases T.exists_binaryTailSkeleton_endpoints hroots with
      ⟨scale, hscale, _, hendpoint⟩
    let S := T.binaryTailSkeleton scale hscale
    refine ⟨S, T.binaryTailOddRoots_subset_realRoots, ?_⟩
    intro y hy
    exact T.binaryTailSignHolds_eval_of_endpoints S
      T.binaryTailOddRoots_subset_realRoots hendpoint hy hroots
  · have hempty : T.realRoots = ∅ := Finset.not_nonempty_iff_eq_empty.mp hroots
    let head₀ : Fin 2 → R := fun i => (T.A (Sum.inl i)).eval 0
    let tail₀ : κ → R := fun j => (T.A (Sum.inr j)).eval 0
    let sign := binaryTailCompressionRequiredSign head₀ tail₀
    let scale : R := if sign = .pos then 1 else -1
    have hscale : scale ≠ 0 := by
      dsimp [scale]
      split <;> simp
    let S : SignedLinearRootSkeleton R :=
      { roots := ∅, scale := scale, scale_ne_zero := hscale }
    have hsignScale : sign.Holds scale := by
      cases hsign : sign <;> simp [scale, hsign, StrictSign.Holds]
    refine ⟨S, by simp [S, hempty], ?_⟩
    intro y _
    let headᵧ : Fin 2 → R := fun i => (T.A (Sum.inl i)).eval y
    let tailᵧ : κ → R := fun j => (T.A (Sum.inr j)).eval y
    have htail₀ (j : κ) : tail₀ j ≠ 0 := by
      apply T.eval_ne_zero_of_not_mem_realRoots
      simp [hempty]
    have htailᵧ (j : κ) : tailᵧ j ≠ 0 := by
      apply T.eval_ne_zero_of_not_mem_realRoots
      simp [hempty]
    have hheadPos (i : Fin 2) : 0 < head₀ i ↔ 0 < headᵧ i := by
      rcases le_total 0 y with hy | hy
      · exact T.coefficient_eval_pos_iff_of_rootFree_Icc hy
          (by simp [hempty]) (Sum.inl i)
      · exact (T.coefficient_eval_pos_iff_of_rootFree_Icc hy
          (by simp [hempty]) (Sum.inl i)).symm
    have htailPos (j : κ) : 0 < tail₀ j ↔ 0 < tailᵧ j := by
      rcases le_total 0 y with hy | hy
      · exact T.coefficient_eval_pos_iff_of_rootFree_Icc hy
          (by simp [hempty]) (Sum.inr j)
      · exact (T.coefficient_eval_pos_iff_of_rootFree_Icc hy
          (by simp [hempty]) (Sum.inr j)).symm
    have hsign : binaryTailCompressionRequiredSign head₀ tail₀ =
        binaryTailCompressionRequiredSign headᵧ tailᵧ :=
      binaryTailCompressionRequiredSign_eq_of_pos_iff
        head₀ tail₀ headᵧ tailᵧ htail₀ htailᵧ hheadPos htailPos
    have hrequired :
        (binaryTailCompressionRequiredSign headᵧ tailᵧ).Holds scale := by
      rw [← hsign]
      exact hsignScale
    simpa [S, SignedLinearRootSkeleton.eval_poly, headᵧ, tailᵧ] using hrequired

end FinitePolynomialState

end

end RatFuncWittLocalGlobal
