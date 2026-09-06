/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Core.Diagonal

/-!
# Diagonal forms over real closed fields

Sign criteria and isotropy lemmas for arbitrary finite diagonal families,
with the ternary specialization used by the local-global base case.
-/

namespace RatFuncWittLocalGlobal

namespace Diagonal

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

theorem isotropic_of_pos_of_neg [Fintype ι] (a : ι → K) {i j : ι}
    (hi : 0 < a i) (hj : a j < 0) :
    Isotropic a := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    exact (not_lt_of_ge hi.le) hj
  have hnonneg : 0 ≤ -a j / a i :=
    div_nonneg (neg_nonneg.mpr hj.le) hi.le
  rcases IsSquare.of_nonneg hnonneg with ⟨r, hr⟩
  have hr' : r ^ 2 = -a j / a i := by
    simpa [sq] using hr.symm
  let x : ι → K := fun k => if k = i then r else if k = j then 1 else 0
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have hxj := congr_fun hx j
    simp [x, hij.symm] at hxj
  · have htotal_eq :
        (∑ k, a k * x k ^ 2) = ∑ k ∈ ({i, j} : Finset ι), a k * x k ^ 2 := by
      symm
      apply Finset.sum_subset (by simp)
      intro k _ hk
      have hki : k ≠ i := by
        intro h
        apply hk
        simp [h]
      have hkj : k ≠ j := by
        intro h
        apply hk
        simp [h]
      simp [x, hki, hkj]
    calc
      (∑ k, a k * x k ^ 2)
          = ∑ k ∈ ({i, j} : Finset ι), a k * x k ^ 2 := htotal_eq
      _ = a i * r ^ 2 + a j := by
            simp [x, hij, hij.symm]
      _ = 0 := by
            rw [hr']
            field_simp [hi.ne']
            ring

omit [IsRealClosed K] in
theorem zero_or_pos_neg_of_isotropic [Fintype ι] {a : ι → K}
    (h : Isotropic a) :
    (∃ i, a i = 0) ∨ ∃ i j, 0 < a i ∧ a j < 0 := by
  classical
  by_cases hzero : ∃ i, a i = 0
  · exact Or.inl hzero
  right
  by_contra hmix
  rcases h with ⟨x, hx_ne, hx_sum⟩
  have hcoeff_ne : ∀ i, a i ≠ 0 := by
    intro i hi
    exact hzero ⟨i, hi⟩
  have hx_exists : ∃ k, x k ≠ 0 := by
    by_contra hx_none
    push Not at hx_none
    exact hx_ne (funext hx_none)
  rcases hx_exists with ⟨k, hxk⟩
  rcases lt_or_gt_of_ne (hcoeff_ne k).symm with hak_pos | hak_neg
  · have hall_pos : ∀ i, 0 < a i := by
      intro i
      rcases lt_or_gt_of_ne (hcoeff_ne i).symm with hai_pos | hai_neg
      · exact hai_pos
      · exact False.elim (hmix ⟨k, i, hak_pos, hai_neg⟩)
    have hsum_pos : 0 < ∑ i, a i * x i ^ 2 := by
      apply Finset.sum_pos'
      · intro i _
        exact mul_nonneg (hall_pos i).le (sq_nonneg _)
      · refine ⟨k, by simp, ?_⟩
        exact mul_pos (hall_pos k) (sq_pos_of_ne_zero hxk)
    simp [hx_sum] at hsum_pos
  · have hall_neg : ∀ i, a i < 0 := by
      intro i
      rcases lt_or_gt_of_ne (hcoeff_ne i).symm with hai_pos | hai_neg
      · exact False.elim (hmix ⟨i, k, hai_pos, hak_neg⟩)
      · exact hai_neg
    have hsum_pos : 0 < ∑ i, -(a i * x i ^ 2) := by
      apply Finset.sum_pos'
      · intro i _
        exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (hall_neg i).le (sq_nonneg _))
      · refine ⟨k, by simp, ?_⟩
        exact neg_pos.mpr (mul_neg_of_neg_of_pos (hall_neg k) (sq_pos_of_ne_zero hxk))
    have hsum_pos' : 0 < -(∑ i, a i * x i ^ 2) := by
      simpa using hsum_pos
    simp [hx_sum] at hsum_pos'

theorem isotropic_iff_zero_or_pos_neg [Fintype ι] (a : ι → K) :
    Isotropic a ↔ (∃ i, a i = 0) ∨ ∃ i j, 0 < a i ∧ a j < 0 := by
  constructor
  · exact zero_or_pos_neg_of_isotropic
  · rintro (⟨i, hi⟩ | ⟨i, j, hi, hj⟩)
    · exact isotropic_of_zero_coeff a hi
    · exact isotropic_of_pos_of_neg a hi hj

theorem all_pos_or_all_neg_of_not_isotropic [Fintype ι] [Nonempty ι] {a : ι → K}
    (hreg : ∀ i, a i ≠ 0) (haniso : ¬ Isotropic a) :
    (∀ i, 0 < a i) ∨ (∀ i, a i < 0) := by
  classical
  have hno_posneg : ¬ ∃ i j, 0 < a i ∧ a j < 0 := by
    intro hposneg
    exact haniso ((isotropic_iff_zero_or_pos_neg a).mpr (Or.inr hposneg))
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  rcases lt_or_gt_of_ne (hreg i₀).symm with hi₀_pos | hi₀_neg
  · left
    intro i
    rcases lt_or_gt_of_ne (hreg i).symm with hi_pos | hi_neg
    · exact hi_pos
    · exact False.elim (hno_posneg ⟨i₀, i, hi₀_pos, hi_neg⟩)
  · right
    intro i
    rcases lt_or_gt_of_ne (hreg i).symm with hi_pos | hi_neg
    · exact False.elim (hno_posneg ⟨i, i₀, hi_pos, hi₀_neg⟩)
    · exact hi_neg

omit [IsRealClosed K] in
theorem not_isotropic_of_all_pos [Fintype ι] {a : ι → K}
    (hpos : ∀ i, 0 < a i) :
    ¬ Isotropic a := by
  intro h
  rcases zero_or_pos_neg_of_isotropic h with hzero | hposneg
  · rcases hzero with ⟨i, hi⟩
    exact (hpos i).ne' hi
  · rcases hposneg with ⟨_, j, _, hj⟩
    exact (not_lt_of_ge (hpos j).le) hj

omit [IsRealClosed K] in
theorem not_isotropic_of_all_neg [Fintype ι] {a : ι → K}
    (hneg : ∀ i, a i < 0) :
    ¬ Isotropic a := by
  intro h
  rcases zero_or_pos_neg_of_isotropic h with hzero | hposneg
  · rcases hzero with ⟨i, hi⟩
    exact (hneg i).ne hi
  · rcases hposneg with ⟨i, _, hi, _⟩
    exact (not_lt_of_ge hi.le) (hneg i)

theorem not_isotropic_iff_all_pos_or_all_neg [Fintype ι] [Nonempty ι]
    {a : ι → K} (hreg : ∀ i, a i ≠ 0) :
    ¬ Isotropic a ↔ (∀ i, 0 < a i) ∨ (∀ i, a i < 0) := by
  constructor
  · exact all_pos_or_all_neg_of_not_isotropic hreg
  · rintro (hpos | hneg)
    · exact not_isotropic_of_all_pos hpos
    · exact not_isotropic_of_all_neg hneg

theorem ternary_isotropic_one_iff (b c : K) :
    TernaryIsotropic 1 b c ↔ b ≤ 0 ∨ c ≤ 0 := by
  let a : Fin 3 → K := ![1, b, c]
  calc
    TernaryIsotropic 1 b c ↔ Isotropic a := by
      simpa [a] using (isotropic_fin_three_iff a).symm
    _ ↔ (∃ i, a i = 0) ∨ ∃ i j, 0 < a i ∧ a j < 0 :=
      isotropic_iff_zero_or_pos_neg a
    _ ↔ b ≤ 0 ∨ c ≤ 0 := by
      constructor
      · rintro (⟨i, hi⟩ | ⟨i, j, hi, hj⟩)
        · fin_cases i <;> simp_all [a]
        · fin_cases j
          · have : (1 : K) < 0 := by simpa [a] using hj
            exact (not_lt_of_ge zero_le_one this).elim
          · exact Or.inl (by simpa [a] using hj.le)
          · exact Or.inr (by simpa [a] using hj.le)
      · rintro (hb | hc)
        · rcases hb.eq_or_lt with rfl | hb
          · exact Or.inl ⟨1, by simp [a]⟩
          · exact Or.inr ⟨0, 1, by simp [a], by simpa [a]⟩
        · rcases hc.eq_or_lt with rfl | hc
          · exact Or.inl ⟨2, by simp [a]⟩
          · exact Or.inr ⟨0, 2, by simp [a], by simpa [a]⟩

end Diagonal

end RatFuncWittLocalGlobal
