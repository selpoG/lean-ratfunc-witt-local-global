/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Polynomial.RealClosedFactorSign

/-!
# Polynomial signs on root-free intervals over a real closed field

The result is algebraic: normalized irreducible factors are either linear or
monic irreducible quadratics.  It therefore does not assume that the ordered
field is conditionally complete.
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u

noncomputable section

/-- A polynomial that is nonzero on a closed interval has the same strict
sign at its two endpoints. -/
theorem polynomial_eval_pos_iff_of_ne_zero_on_Icc
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R]
    {p : R[X]} {x y : R} (hxy : x ≤ y)
    (hzero : ∀ z ∈ Set.Icc x y, p.eval z ≠ 0) :
    0 < p.eval x ↔ 0 < p.eval y := by
  have hp0 : p ≠ 0 := by
    intro hp
    exact hzero x (Set.left_mem_Icc.mpr hxy) (by simp [hp])
  let m := UniqueFactorizationMonoid.normalizedFactors p
  have hfactor : ∀ π ∈ m, 0 < π.eval x * π.eval y := by
    intro π hπ
    exact normalizedFactor_eval_mul_eval_pos_of_polynomial_ne_zero_on_Icc
      hxy hπ hzero
  have hprod :
      0 < (m.map (fun π : R[X] => π.eval x * π.eval y)).prod := by
    apply Multiset.prod_pos
    intro z hz
    obtain ⟨π, hπ, rfl⟩ := Multiset.mem_map.mp hz
    exact hfactor π hπ
  rw [Multiset.prod_map_mul] at hprod
  have hfactor_x :
      p.leadingCoeff * (m.map (Polynomial.eval x)).prod = p.eval x := by
    simpa [m, Polynomial.eval_mul, Polynomial.eval_multiset_prod] using
      congrArg (fun q : R[X] => q.eval x)
        (Polynomial.leadingCoeff_mul_prod_normalizedFactors p)
  have hfactor_y :
      p.leadingCoeff * (m.map (Polynomial.eval y)).prod = p.eval y := by
    simpa [m, Polynomial.eval_mul, Polynomial.eval_multiset_prod] using
      congrArg (fun q : R[X] => q.eval y)
        (Polynomial.leadingCoeff_mul_prod_normalizedFactors p)
  have hlc : 0 < p.leadingCoeff * p.leadingCoeff :=
    mul_self_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  have hxypos : 0 < p.eval x * p.eval y := by
    calc
      0 < (p.leadingCoeff * p.leadingCoeff) *
          ((m.map (Polynomial.eval x)).prod * (m.map (Polynomial.eval y)).prod) :=
        mul_pos hlc hprod
      _ = (p.leadingCoeff * (m.map (Polynomial.eval x)).prod) *
          (p.leadingCoeff * (m.map (Polynomial.eval y)).prod) := by ring
      _ = p.eval x * p.eval y := by rw [hfactor_x, hfactor_y]
  constructor
  · intro hx
    rcases (mul_pos_iff.mp hxypos) with ⟨_, hy⟩ | ⟨hxneg, _⟩
    · exact hy
    · exact (lt_asymm hx hxneg).elim
  · intro hy
    rcases (mul_pos_iff.mp hxypos) with ⟨hx, _⟩ | ⟨_, hyneg⟩
    · exact hx
    · exact (lt_asymm hy hyneg).elim

/-- At a simple root forming the left endpoint of a root-free interval, the
right-hand sign is the sign of the cofactor at that root. -/
theorem polynomial_divByMonic_eval_pos_iff_eval_pos_of_squarefree_of_isRoot_of_ne_zero_on_Ioc
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R]
    {p : R[X]} {r s : R} (hp : Squarefree p) (hroot : p.IsRoot r)
    (hrs : r < s) (hzero : ∀ z ∈ Set.Ioc r s, p.eval z ≠ 0) :
    0 < (p /ₘ (X - C r)).eval r ↔ 0 < p.eval s := by
  let q := p /ₘ (X - C r)
  have hqroot : q.eval r ≠ 0 :=
    eval_divByMonic_X_sub_C_ne_zero_of_squarefree_of_isRoot hp hroot
  have hp_factor : (X - C r) * q = p := by
    exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hqzero : ∀ z ∈ Set.Icc r s, q.eval z ≠ 0 := by
    intro z hz
    by_cases hzr : z = r
    · simpa [hzr] using hqroot
    · intro hqz
      apply hzero z ⟨lt_of_le_of_ne hz.1 (Ne.symm hzr), hz.2⟩
      rw [← hp_factor, Polynomial.eval_mul, hqz, mul_zero]
  have hqsign : 0 < q.eval r ↔ 0 < q.eval s :=
    polynomial_eval_pos_iff_of_ne_zero_on_Icc hrs.le hqzero
  change 0 < q.eval r ↔ 0 < p.eval s
  rw [← hp_factor, Polynomial.eval_mul]
  simp only [eval_sub, eval_X, eval_C]
  constructor
  · intro hqr
    exact mul_pos (sub_pos.mpr hrs) (hqsign.mp hqr)
  · intro hmul
    exact hqsign.mpr (pos_of_mul_pos_right hmul (sub_nonneg.mpr hrs.le))

/-- At a simple root forming the right endpoint of a root-free interval, the
left-hand sign is the sign of the negatively oriented cofactor. -/
theorem polynomial_eval_pos_iff_neg_divByMonic_eval_of_squarefree_of_isRoot_of_ne_zero_on_Ico
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R]
    {p : R[X]} {r s : R} (hp : Squarefree p) (hroot : p.IsRoot s)
    (hrs : r < s) (hzero : ∀ z ∈ Set.Ico r s, p.eval z ≠ 0) :
    0 < p.eval r ↔ 0 < -(p /ₘ (X - C s)).eval s := by
  let q := p /ₘ (X - C s)
  have hqroot : q.eval s ≠ 0 :=
    eval_divByMonic_X_sub_C_ne_zero_of_squarefree_of_isRoot hp hroot
  have hp_factor : (X - C s) * q = p := by
    exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hqzero : ∀ z ∈ Set.Icc r s, q.eval z ≠ 0 := by
    intro z hz
    by_cases hzs : z = s
    · simpa [hzs] using hqroot
    · intro hqz
      apply hzero z ⟨hz.1, lt_of_le_of_ne hz.2 hzs⟩
      rw [← hp_factor, Polynomial.eval_mul, hqz, mul_zero]
  have hqsign : 0 < (-q).eval r ↔ 0 < (-q).eval s :=
    polynomial_eval_pos_iff_of_ne_zero_on_Icc hrs.le (by
      intro z hz
      simpa using hqzero z hz)
  have hqneg : q.eval r < 0 ↔ q.eval s < 0 := by
    simpa using hqsign
  change 0 < p.eval r ↔ 0 < -q.eval s
  rw [← hp_factor, Polynomial.eval_mul]
  simp only [eval_sub, eval_X, eval_C, neg_pos]
  constructor
  · intro hmul
    have hqr : q.eval r < 0 :=
      neg_of_mul_pos_right hmul (sub_nonpos.mpr hrs.le)
    exact hqneg.mp hqr
  · intro hqs
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hrs) (hqneg.mpr hqs)

end
end RatFuncWittLocalGlobal
