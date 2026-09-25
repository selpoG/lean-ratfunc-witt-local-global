/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.FiniteDimensional.Core

/-!
# Algebraic reconstruction for binary-tail compression

This file contains the coordinate algebra used by the dimension-reduction
step.  If the tail enlarged by `-c` is isotropic, its last coordinate either
vanishes and exposes an isotropic tail, or represents a nonzero square multiple
of `c`.  In the latter case an isotropic ternary head reconstructs isotropy of
the original binary-plus-tail form.
-/

open scoped BigOperators

namespace RatFuncWittLocalGlobal

namespace Diagonal

variable {F κ : Type*}

/-- An isotropic tail enlarged by `-c`, together with an isotropic ternary
head `<a,b,c>`, reconstructs isotropy of the original binary-plus-tail form. -/
theorem isotropic_sumType_of_ternary_of_tailAdjoinNeg
    [Field F] [Fintype κ]
    (a b c : F) (hc : c ≠ 0) (ψ : κ → F)
    (htern : TernaryIsotropic a b c)
    (htail : Isotropic (Sum.elim ψ (fun _ : Fin 1 => -c))) :
    Isotropic (sumTypeCoeff a b ψ) := by
  rcases htail with ⟨z, hz, hzero⟩
  let y : κ → F := fun i => z (Sum.inl i)
  let t : F := z (Sum.inr 0)
  have hvalue : (∑ i, ψ i * y i ^ 2) - c * t ^ 2 = 0 := by
    rw [Fintype.sum_sum_type] at hzero
    simpa [y, t, Fin.sum_univ_one, sub_eq_add_neg] using hzero
  by_cases ht : t = 0
  · apply isotropic_sumType_of_tail a b ψ
    refine ⟨y, ?_, ?_⟩
    · intro hy
      apply hz
      funext k
      cases k with
      | inl i => exact congr_fun hy i
      | inr j =>
          fin_cases j
          exact ht
    · simpa [ht] using hvalue
  · have hy : y ≠ 0 := by
      intro hy
      have hct : c * t ^ 2 = 0 := by
        simpa [hy] using hvalue
      exact hc (mul_eq_zero.mp hct |>.resolve_right (pow_ne_zero 2 ht))
    have hrep : c * t ^ 2 = ∑ i, ψ i * y i ^ 2 := by
      exact (sub_eq_zero.mp hvalue).symm
    have htern' : TernaryIsotropic a b (c * t ^ 2) := by
      simpa using (ternary_isotropic_mul_square
        (a₀ := a) (a₁ := b) (a₂ := c)
        (u₀ := 1) (u₁ := 1) (u₂ := t)
        one_ne_zero one_ne_zero ht).2 htern
    exact isotropic_sumType_of_ternary_of_representation
      a b (c * t ^ 2) ψ y hy hrep htern'

end Diagonal

end RatFuncWittLocalGlobal
