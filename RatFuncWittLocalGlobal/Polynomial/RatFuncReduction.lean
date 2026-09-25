/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Core.Diagonal
import RatFuncWittLocalGlobal.Core.RatFunc

/-!
# Reductions from rational functions to polynomials
-/

open scoped BigOperators

namespace RatFuncWittLocalGlobal

namespace RatFunc

variable {R ι : Type*}

private theorem exists_polynomial_solution_of_diagonal_isotropic
    [Field R] [Fintype ι] {a : ι → RatFunc R}
    (h : Diagonal.Isotropic a) :
    ∃ p : ι → Polynomial R,
      p ≠ 0 ∧
        ∑ i, a i * (algebraMap (Polynomial R) (RatFunc R) (p i)) ^ 2 = 0 := by
  classical
  rcases h with ⟨x, hx_ne, hx_sum⟩
  obtain ⟨d, hd, hd_spec⟩ := exists_common_denominator x
  choose p hp using hd_spec
  refine ⟨p, ?_, ?_⟩
  · intro hp_zero
    apply hx_ne
    funext i
    rw [hp i, congr_fun hp_zero i]
    simp
  · let D : RatFunc R := algebraMap (Polynomial R) (RatFunc R) d
    have hD : D ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hd
    have hx_sum' :
        ∑ i, a i * (algebraMap (Polynomial R) (RatFunc R) (p i) / D) ^ 2 = 0 := by
      simpa [D, hp] using hx_sum
    calc
      ∑ i, a i * (algebraMap (Polynomial R) (RatFunc R) (p i)) ^ 2
          = D ^ 2 *
              (∑ i, a i * (algebraMap (Polynomial R) (RatFunc R) (p i) / D) ^ 2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              field_simp [hD]
      _ = 0 := by simp [hx_sum']

private theorem exists_polynomial_solution_of_ternary_isotropic
    [Field R] {a₀ a₁ a₂ : RatFunc R}
    (h : Diagonal.TernaryIsotropic a₀ a₁ a₂) :
    ∃ p₀ p₁ p₂ : Polynomial R,
      (p₀ ≠ 0 ∨ p₁ ≠ 0 ∨ p₂ ≠ 0) ∧
        a₀ * (algebraMap (Polynomial R) (RatFunc R) p₀) ^ 2 +
        a₁ * (algebraMap (Polynomial R) (RatFunc R) p₁) ^ 2 +
        a₂ * (algebraMap (Polynomial R) (RatFunc R) p₂) ^ 2 = 0 := by
  classical
  have hdiag : Diagonal.Isotropic (![a₀, a₁, a₂] : Fin 3 → RatFunc R) := by
    simpa using
      (Diagonal.isotropic_fin_three_iff (![a₀, a₁, a₂] : Fin 3 → RatFunc R)).mpr h
  rcases exists_polynomial_solution_of_diagonal_isotropic hdiag with ⟨p, hp_ne, hp_sum⟩
  refine ⟨p 0, p 1, p 2, ?_, ?_⟩
  · by_contra hp_all
    simp only [not_or, not_not] at hp_all
    apply hp_ne
    funext i
    fin_cases i <;> simp [hp_all]
  · simpa [Fin.sum_univ_three] using hp_sum

private theorem ternary_isotropic_of_polynomial_solution
    [Field R] {a₀ a₁ a₂ : RatFunc R}
    {p₀ p₁ p₂ : Polynomial R}
    (hp_ne : p₀ ≠ 0 ∨ p₁ ≠ 0 ∨ p₂ ≠ 0)
    (hp_sum :
      a₀ * (algebraMap (Polynomial R) (RatFunc R) p₀) ^ 2 +
      a₁ * (algebraMap (Polynomial R) (RatFunc R) p₁) ^ 2 +
      a₂ * (algebraMap (Polynomial R) (RatFunc R) p₂) ^ 2 = 0) :
    Diagonal.TernaryIsotropic a₀ a₁ a₂ := by
  refine ⟨algebraMap (Polynomial R) (RatFunc R) p₀,
    algebraMap (Polynomial R) (RatFunc R) p₁,
    algebraMap (Polynomial R) (RatFunc R) p₂, ?_, hp_sum⟩
  rcases hp_ne with hp₀ | hp₁ | hp₂
  · exact Or.inl fun h ↦ hp₀ ((_root_.RatFunc.algebraMap_injective R) (by simpa using h))
  · exact Or.inr <| Or.inl fun h ↦ hp₁ ((_root_.RatFunc.algebraMap_injective R) (by simpa using h))
  · exact Or.inr <| Or.inr fun h ↦ hp₂ ((_root_.RatFunc.algebraMap_injective R) (by simpa using h))

theorem ternary_isotropic_iff_exists_polynomial_solution
    [Field R] {a₀ a₁ a₂ : RatFunc R} :
    Diagonal.TernaryIsotropic a₀ a₁ a₂ ↔
      ∃ p₀ p₁ p₂ : Polynomial R,
        (p₀ ≠ 0 ∨ p₁ ≠ 0 ∨ p₂ ≠ 0) ∧
          a₀ * (algebraMap (Polynomial R) (RatFunc R) p₀) ^ 2 +
          a₁ * (algebraMap (Polynomial R) (RatFunc R) p₁) ^ 2 +
          a₂ * (algebraMap (Polynomial R) (RatFunc R) p₂) ^ 2 = 0 := by
  constructor
  · exact exists_polynomial_solution_of_ternary_isotropic
  · rintro ⟨p₀, p₁, p₂, hp_ne, hp_sum⟩
    exact ternary_isotropic_of_polynomial_solution hp_ne hp_sum

private theorem binary_representation_of_polynomial_solution
    [Field R] {c t : RatFunc R} {p q d : Polynomial R}
    (hd : d ≠ 0)
    (hpq :
      (algebraMap (Polynomial R) (RatFunc R) p) ^ 2 +
        c * (algebraMap (Polynomial R) (RatFunc R) q) ^ 2 =
          t * (algebraMap (Polynomial R) (RatFunc R) d) ^ 2) :
    ∃ y z : RatFunc R, y ^ 2 + c * z ^ 2 = t := by
  let D : RatFunc R := algebraMap (Polynomial R) (RatFunc R) d
  have hD : D ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hd
  refine ⟨algebraMap (Polynomial R) (RatFunc R) p / D,
    algebraMap (Polynomial R) (RatFunc R) q / D, ?_⟩
  have hmul :
      ((algebraMap (Polynomial R) (RatFunc R) p / D) ^ 2 +
        c * (algebraMap (Polynomial R) (RatFunc R) q / D) ^ 2) * D ^ 2 =
          t * D ^ 2 := by
    calc
      ((algebraMap (Polynomial R) (RatFunc R) p / D) ^ 2 +
          c * (algebraMap (Polynomial R) (RatFunc R) q / D) ^ 2) * D ^ 2
          =
            (algebraMap (Polynomial R) (RatFunc R) p) ^ 2 +
              c * (algebraMap (Polynomial R) (RatFunc R) q) ^ 2 := by
              field_simp [hD]
      _ = t * D ^ 2 := by simpa [D] using hpq
  exact (mul_right_injective₀ (pow_ne_zero 2 hD))
    (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)

private theorem exists_polynomial_solution_of_binary_representation
    [Field R] {c t : RatFunc R}
    (h : ∃ y z : RatFunc R, y ^ 2 + c * z ^ 2 = t) :
    ∃ p q d : Polynomial R,
      d ≠ 0 ∧
        (algebraMap (Polynomial R) (RatFunc R) p) ^ 2 +
          c * (algebraMap (Polynomial R) (RatFunc R) q) ^ 2 =
            t * (algebraMap (Polynomial R) (RatFunc R) d) ^ 2 := by
  classical
  rcases h with ⟨y, z, hyz⟩
  let x : Fin 2 → RatFunc R := fun i => if i = 0 then y else z
  rcases exists_common_denominator (R := R) (ι := Fin 2) x with ⟨d, hd, hden⟩
  rcases hden 0 with ⟨p, hp⟩
  rcases hden 1 with ⟨q, hq⟩
  let D : RatFunc R := algebraMap (Polynomial R) (RatFunc R) d
  have hD : D ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hd
  have hy_rep : y = algebraMap (Polynomial R) (RatFunc R) p / D := by
    simpa [x, D] using hp
  have hz_rep : z = algebraMap (Polynomial R) (RatFunc R) q / D := by
    simpa [x, D] using hq
  have hp_mul : algebraMap (Polynomial R) (RatFunc R) p = y * D := by
    rw [hy_rep]
    field_simp [hD]
  have hq_mul : algebraMap (Polynomial R) (RatFunc R) q = z * D := by
    rw [hz_rep]
    field_simp [hD]
  refine ⟨p, q, d, hd, ?_⟩
  calc
    (algebraMap (Polynomial R) (RatFunc R) p) ^ 2 +
        c * (algebraMap (Polynomial R) (RatFunc R) q) ^ 2
        = (y ^ 2 + c * z ^ 2) * D ^ 2 := by
          rw [hp_mul, hq_mul]
          ring
    _ = t * (algebraMap (Polynomial R) (RatFunc R) d) ^ 2 := by
          rw [hyz]

theorem binary_representation_iff_exists_polynomial_solution
    [Field R] {c t : RatFunc R} :
    (∃ y z : RatFunc R, y ^ 2 + c * z ^ 2 = t) ↔
      ∃ p q d : Polynomial R,
        d ≠ 0 ∧
          (algebraMap (Polynomial R) (RatFunc R) p) ^ 2 +
            c * (algebraMap (Polynomial R) (RatFunc R) q) ^ 2 =
              t * (algebraMap (Polynomial R) (RatFunc R) d) ^ 2 := by
  constructor
  · exact exists_polynomial_solution_of_binary_representation
  · rintro ⟨p, q, d, hd, hpq⟩
    exact binary_representation_of_polynomial_solution hd hpq

end RatFunc

end RatFuncWittLocalGlobal
