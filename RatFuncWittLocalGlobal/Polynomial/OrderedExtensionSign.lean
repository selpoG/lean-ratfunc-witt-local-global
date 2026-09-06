/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Polynomial.GapSign
import RatFuncWittLocalGlobal.Polynomial.Positivity

/-!
# Polynomial signs in ordered field extensions

A finite collection of base-field roots cuts every ordered extension point
into the same finite cells as an ordinary base-field sample.  Together with
the positivity of monic irreducible quadratics over a real closed field, this
transports polynomial signs back to that sample point.
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u v

noncomputable section

/-- An ordered extension point avoiding a finite set of base points has an
ordinary base-field sample with exactly the same comparisons to that set. -/
theorem exists_base_sample_with_same_finite_cut
    {R : Type u} {K : Type v}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (φ : R →+* K) (hφ : StrictMono φ) (s : Finset R) (x : K)
    (hx : ∀ r ∈ s, x ≠ φ r) :
    ∃ y : R, y ∉ s ∧
      ∀ r ∈ s, (r < y ↔ φ r < x) ∧ (y < r ↔ x < φ r) := by
  classical
  let lower := s.filter (fun r => φ r < x)
  by_cases hlower : lower.Nonempty
  · let r := lower.max' hlower
    have hrLower : r ∈ lower := lower.max'_mem hlower
    have hrS : r ∈ s := (Finset.mem_filter.mp hrLower).1
    have hrx : φ r < x := (Finset.mem_filter.mp hrLower).2
    let upper := s.filter (fun t => x < φ t)
    by_cases hupper : upper.Nonempty
    · let t := upper.min' hupper
      have htUpper : t ∈ upper := upper.min'_mem hupper
      have htS : t ∈ s := (Finset.mem_filter.mp htUpper).1
      have hxt : x < φ t := (Finset.mem_filter.mp htUpper).2
      have hrt : r < t := hφ.lt_iff_lt.mp (hrx.trans hxt)
      let y := (r + t) / 2
      have hry : r < y := by dsimp [y]; linarith
      have hyt : y < t := by dsimp [y]; linarith
      refine ⟨y, ?_, ?_⟩
      · intro hyS
        by_cases hyx : φ y < x
        · have hyLower : y ∈ lower := Finset.mem_filter.mpr ⟨hyS, hyx⟩
          exact (not_lt_of_ge (lower.le_max' y hyLower)) hry
        · have hxy : x < φ y := lt_of_le_of_ne (le_of_not_gt hyx) (hx y hyS)
          have hyUpper : y ∈ upper := Finset.mem_filter.mpr ⟨hyS, hxy⟩
          exact (not_lt_of_ge (upper.min'_le y hyUpper)) hyt
      · intro z hzS
        have hzCut : φ z < x ∨ x < φ z := lt_or_gt_of_ne (hx z hzS).symm
        constructor
        · constructor
          · intro hzy
            rcases hzCut with hzx | hxz
            · exact hzx
            · have hzUpper : z ∈ upper := Finset.mem_filter.mpr ⟨hzS, hxz⟩
              have htz : t ≤ z := upper.min'_le z hzUpper
              exact ((not_lt_of_ge (hyt.le.trans htz)) hzy).elim
          · intro hzx
            have hzLower : z ∈ lower := Finset.mem_filter.mpr ⟨hzS, hzx⟩
            exact (lower.le_max' z hzLower).trans_lt hry
        · constructor
          · intro hyz
            rcases hzCut with hzx | hxz
            · have hzLower : z ∈ lower := Finset.mem_filter.mpr ⟨hzS, hzx⟩
              have hzr : z ≤ r := lower.le_max' z hzLower
              exact ((not_lt_of_ge (hzr.trans hry.le)) hyz).elim
            · exact hxz
          · intro hxz
            have hzUpper : z ∈ upper := Finset.mem_filter.mpr ⟨hzS, hxz⟩
            exact hyt.trans_le (upper.min'_le z hzUpper)
    · let y := r + 1
      have hry : r < y := by simp [y]
      refine ⟨y, ?_, ?_⟩
      · intro hyS
        have hxy : x < φ y := by
          have hnot : ¬φ y < x := by
            intro hyx
            exact (not_lt_of_ge (lower.le_max' y
              (Finset.mem_filter.mpr ⟨hyS, hyx⟩))) hry
          exact lt_of_le_of_ne (le_of_not_gt hnot) (hx y hyS)
        exact hupper ⟨y, Finset.mem_filter.mpr ⟨hyS, hxy⟩⟩
      · intro z hzS
        have hzx : φ z < x := by
          have hnot : ¬x < φ z := fun hxz =>
            hupper ⟨z, Finset.mem_filter.mpr ⟨hzS, hxz⟩⟩
          exact lt_of_le_of_ne (le_of_not_gt hnot) (hx z hzS).symm
        have hzLower : z ∈ lower := Finset.mem_filter.mpr ⟨hzS, hzx⟩
        have hzy : z < y := (lower.le_max' z hzLower).trans_lt hry
        exact ⟨⟨fun _ => hzx, fun _ => hzy⟩,
          ⟨fun hyz => (not_lt_of_ge hzy.le hyz).elim,
            fun hxz => (lt_asymm hzx hxz).elim⟩⟩
  · by_cases hs : s.Nonempty
    · let t := s.min' hs
      have htS : t ∈ s := s.min'_mem hs
      have hxt : x < φ t := by
        have hnot : ¬φ t < x := fun htx =>
          hlower ⟨t, Finset.mem_filter.mpr ⟨htS, htx⟩⟩
        exact lt_of_le_of_ne (le_of_not_gt hnot) (hx t htS)
      let y := t - 1
      have hyt : y < t := by simp [y]
      refine ⟨y, ?_, ?_⟩
      · intro hyS
        have hyx : φ y < x := by
          have hnot : ¬x < φ y := by
            intro hxy
            have hty : t ≤ y := s.min'_le y hyS
            exact ((not_lt_of_ge hty) hyt).elim
          exact lt_of_le_of_ne (le_of_not_gt hnot) (hx y hyS).symm
        exact hlower ⟨y, Finset.mem_filter.mpr ⟨hyS, hyx⟩⟩
      · intro z hzS
        have hxz : x < φ z := by
          have hnot : ¬φ z < x := fun hzx =>
            hlower ⟨z, Finset.mem_filter.mpr ⟨hzS, hzx⟩⟩
          exact lt_of_le_of_ne (le_of_not_gt hnot) (hx z hzS)
        have hyz : y < z := hyt.trans_le (s.min'_le z hzS)
        exact ⟨⟨fun hzy => (not_lt_of_ge hyz.le hzy).elim,
            fun hzx => (lt_asymm hxz hzx).elim⟩,
          ⟨fun _ => hxz, fun _ => hyz⟩⟩
    · have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      exact ⟨0, by simp [hsEmpty], by simp [hsEmpty]⟩

/-- A monic irreducible quadratic over a real closed field remains strictly
positive at every point of every ordered field extension. -/
theorem eval₂_pos_of_irreducible_monic_natDegree_two
    {R : Type u} {K : Type v}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (φ : R →+* K) (hφ : StrictMono φ) {π : Polynomial R}
    (hirr : Irreducible π) (hmonic : π.Monic) (hdeg : π.natDegree = 2)
    (x : K) :
    0 < π.eval₂ φ x := by
  have hπeq :=
    RatFunc.Polynomial.eq_monic_quadratic_of_natDegree_eq_two hmonic hdeg
  have hquad : Irreducible
      (X ^ 2 + C (π.coeff 1) * X + C (π.coeff 0) : Polynomial R) := by
    simpa [← hπeq] using hirr
  have hconst : 0 < φ (π.coeff 0 - (π.coeff 1 / 2) ^ 2) := by
    simpa using
      hφ (RatFunc.monic_quadratic_completed_square_pos_of_irreducible hquad)
  rw [hπeq]
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
  have hsquare : 0 ≤ (x + φ (π.coeff 1 / 2)) ^ 2 := sq_nonneg _
  have hmapTwo : φ (π.coeff 1 / 2) = φ (π.coeff 1) / 2 := by
    rw [map_div₀, map_ofNat]
  have hmapConst :
      φ (π.coeff 0 - (π.coeff 1 / 2) ^ 2) =
        φ (π.coeff 0) - (φ (π.coeff 1) / 2) ^ 2 := by
    rw [map_sub, map_pow, hmapTwo]
  rw [hmapTwo] at hsquare
  rw [hmapConst] at hconst
  nlinarith

/-- If a finite set contains every real root of a nonzero polynomial, then
two points lying in the same cell cut out by that set give the same strict
sign, even when one point belongs to an ordered field extension. -/
theorem polynomial_eval₂_pos_iff_eval_of_same_finite_cut
    {R : Type u} {K : Type v}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (φ : R →+* K) (hφ : StrictMono φ) (s : Finset R)
    {x : K} {y : R} (p : Polynomial R) (hp : p ≠ 0)
    (hx : ∀ r ∈ s, x ≠ φ r)
    (hroots : ∀ r : R, p.eval r = 0 → r ∈ s)
    (hcut : ∀ r ∈ s, (r < y ↔ φ r < x) ∧ (y < r ↔ x < φ r)) :
    0 < p.eval₂ φ x ↔ 0 < p.eval y := by
  classical
  let m := UniqueFactorizationMonoid.normalizedFactors p
  have hfactor : ∀ π ∈ m, 0 < π.eval₂ φ x * π.eval₂ φ (φ y) := by
    intro π hπ
    have hπirr : Irreducible π :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor π hπ
    have hπmonic : π.Monic := monic_of_mem_normalizedFactors hπ
    by_cases hdeg : π.natDegree = 1
    · obtain ⟨r, rfl⟩ :=
        exists_eq_X_sub_C_of_irreducible_monic_of_natDegree_eq_one
          hπirr hπmonic hdeg
      have hrRoot : p.eval r = 0 :=
        eval_eq_zero_of_dvd_of_eval_eq_zero
          (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hπ) (by simp)
      have hrS : r ∈ s := hroots r hrRoot
      have hcuts := hcut r hrS
      have hry : r < y ∨ y < r := by
        rcases lt_trichotomy r y with hry | hry | hyr
        · exact Or.inl hry
        · subst y
          have hnotLeft : ¬φ r < x := fun hrx =>
            (lt_irrefl r) (hcuts.1.mpr hrx)
          have hnotRight : ¬x < φ r := fun hxr =>
            (lt_irrefl r) (hcuts.2.mpr hxr)
          exact (hx r hrS
            (le_antisymm (le_of_not_gt hnotLeft) (le_of_not_gt hnotRight))).elim
        · exact Or.inr hyr
      rcases hry with hry | hyr
      · have hrx : φ r < x := hcuts.1.mp hry
        have hry' : φ r < φ y := hφ hry
        simpa using mul_pos (sub_pos.mpr hrx) (sub_pos.mpr hry')
      · have hxr : x < φ r := hcuts.2.mp hyr
        have hyr' : φ y < φ r := hφ hyr
        simpa using mul_pos_of_neg_of_neg (sub_neg.mpr hxr) (sub_neg.mpr hyr')
    · have hdegLe : π.natDegree ≤ 2 :=
        RatFunc.irreducibleNatDegreeLeTwo_of_realClosed π hπirr
      have hdegTwo : π.natDegree = 2 := by
        have hdegPos : 0 < π.natDegree :=
          Polynomial.natDegree_pos_iff_degree_pos.mpr
            (Polynomial.degree_pos_of_irreducible hπirr)
        omega
      have hxpos := eval₂_pos_of_irreducible_monic_natDegree_two
        φ hφ hπirr hπmonic hdegTwo x
      have hypos : 0 < π.eval₂ φ (φ y) :=
        eval₂_pos_of_irreducible_monic_natDegree_two
          φ hφ hπirr hπmonic hdegTwo (φ y)
      exact mul_pos hxpos hypos
  have hprod :
      0 < (m.map (fun π : Polynomial R =>
        π.eval₂ φ x * π.eval₂ φ (φ y))).prod := by
    apply Multiset.prod_pos
    intro z hz
    obtain ⟨π, hπ, rfl⟩ := Multiset.mem_map.mp hz
    exact hfactor π hπ
  rw [Multiset.prod_map_mul] at hprod
  have hlcMap : φ p.leadingCoeff ≠ 0 := by
    intro hz
    exact (leadingCoeff_ne_zero.mpr hp)
      (RingHom.injective φ (by simpa using hz))
  have hlc : 0 < φ p.leadingCoeff * φ p.leadingCoeff :=
    mul_self_pos.mpr hlcMap
  have hfactorK :
      φ p.leadingCoeff * (m.map (fun π : Polynomial R => π.eval₂ φ x)).prod =
        p.eval₂ φ x := by
    simpa [m, Polynomial.eval₂_mul, Polynomial.eval₂_multiset_prod] using
      congrArg (fun q : Polynomial R => q.eval₂ φ x)
        (Polynomial.leadingCoeff_mul_prod_normalizedFactors p)
  have hfactorY :
      φ p.leadingCoeff *
          (m.map (fun π : Polynomial R => π.eval₂ φ (φ y))).prod =
        p.eval₂ φ (φ y) := by
    simpa [m, Polynomial.eval₂_mul, Polynomial.eval₂_multiset_prod] using
      congrArg (fun q : Polynomial R => q.eval₂ φ (φ y))
        (Polynomial.leadingCoeff_mul_prod_normalizedFactors p)
  have hxy : 0 < p.eval₂ φ x * p.eval₂ φ (φ y) := by
    calc
      0 < (φ p.leadingCoeff * φ p.leadingCoeff) *
          ((m.map (fun π : Polynomial R => π.eval₂ φ x)).prod *
            (m.map (fun π : Polynomial R => π.eval₂ φ (φ y))).prod) :=
        mul_pos hlc hprod
      _ = (φ p.leadingCoeff *
            (m.map (fun π : Polynomial R => π.eval₂ φ x)).prod) *
          (φ p.leadingCoeff *
            (m.map (fun π : Polynomial R => π.eval₂ φ (φ y))).prod) := by ring
      _ = p.eval₂ φ x * p.eval₂ φ (φ y) := by rw [hfactorK, hfactorY]
  have hmapEval : p.eval₂ φ (φ y) = φ (p.eval y) := by simp
  have hφpos : 0 < φ (p.eval y) ↔ 0 < p.eval y := by
    simpa using hφ.lt_iff_lt (a := 0) (b := p.eval y)
  rw [← hφpos, ← hmapEval]
  constructor
  · intro hxpos
    rcases (mul_pos_iff.mp hxy) with ⟨_, hypos⟩ | ⟨hxneg, _⟩
    · exact hypos
    · exact (lt_asymm hxpos hxneg).elim
  · intro hypos
    rcases (mul_pos_iff.mp hxy) with ⟨hxpos, _⟩ | ⟨_, hyneg⟩
    · exact hxpos
    · exact (lt_asymm hypos hyneg).elim

end

end RatFuncWittLocalGlobal
