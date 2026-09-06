/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Core.Diagonal
import RatFuncWittLocalGlobal.Ordering.Basic

/-!
# Finite-dimensional diagonal definiteness and reconstruction

This file records the strict-sign characterization of definite diagonal forms
and the elementary sum-type construction that replaces a represented diagonal
coefficient by its representing finite vector.
-/

open scoped BigOperators

namespace RatFuncWittLocalGlobal

namespace Diagonal

variable {F ι κ : Type*}

/-! ### Ordered diagonal values -/

/-- The value of the diagonal form with coefficient vector `a` at `x`. -/
def diagonalValue [Field F] [Fintype ι] (a x : ι → F) : F :=
  ∑ i, a i * x i ^ 2

/-- The diagonal coefficients obtained by adjoining a binary form to a tail. -/
def sumTypeCoeff (a b : F) (ψ : κ → F) : Fin 2 ⊕ κ → F :=
  Sum.elim ![a, b] ψ

/-- An isotropic tail embeds into the binary-plus-tail diagonal form. -/
theorem isotropic_sumType_of_tail [Field F] [Fintype κ]
    (a b : F) (ψ : κ → F) (hψ : Isotropic ψ) :
    Isotropic (sumTypeCoeff a b ψ) := by
  rcases hψ with ⟨y, hy, hsum⟩
  let z : Fin 2 ⊕ κ → F := Sum.elim (fun _ => 0) y
  refine ⟨z, ?_, ?_⟩
  · intro hz
    apply hy
    funext i
    exact congr_fun hz (Sum.inr i)
  · rw [Fintype.sum_sum_type]
    simpa [sumTypeCoeff, z, Fin.sum_univ_two] using hsum

/--
If `c` is represented by a nonzero tail vector and `<a,b,c>` is isotropic,
then adjoining that tail to the first two coefficients gives an isotropic
finite diagonal form.
-/
theorem isotropic_sumType_of_ternary_of_representation [Field F] [Fintype κ]
    (a b c : F) (ψ : κ → F) (y : κ → F) (hy : y ≠ 0)
    (hrep : c = ∑ i, ψ i * y i ^ 2)
    (htern : TernaryIsotropic a b c) :
    Isotropic (sumTypeCoeff a b ψ) := by
  rcases htern with ⟨x₀, x₁, x₂, hx, hsum⟩
  let z : Fin 2 ⊕ κ → F := Sum.elim ![x₀, x₁] (fun i => x₂ * y i)
  refine ⟨z, ?_, ?_⟩
  · intro hz
    rcases hx with hx₀ | hx₁ | hx₂
    · exact hx₀ (by simpa [z] using congr_fun hz (Sum.inl 0))
    · exact hx₁ (by simpa [z] using congr_fun hz (Sum.inl 1))
    · obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
        by_contra hzero
        apply hy
        funext i
        by_contra hi
        exact hzero ⟨i, hi⟩
      have hzi : x₂ * y i = 0 := by
        simpa only [z, Sum.elim_inr, Pi.zero_apply] using congr_fun hz (Sum.inr i)
      exact hx₂ (mul_eq_zero.mp hzi |>.resolve_right hi)
  · rw [Fintype.sum_sum_type]
    simp only [sumTypeCoeff, z, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two]
    calc
      a * x₀ ^ 2 + b * x₁ ^ 2 + ∑ i, ψ i * (x₂ * y i) ^ 2
          = a * x₀ ^ 2 + b * x₁ ^ 2 + x₂ ^ 2 * ∑ i, ψ i * y i ^ 2 := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = a * x₀ ^ 2 + b * x₁ ^ 2 + c * x₂ ^ 2 := by
            rw [hrep]
            ring
      _ = 0 := hsum

end Diagonal

end RatFuncWittLocalGlobal
