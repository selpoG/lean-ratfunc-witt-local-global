/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Core.Basic

/-!
# Diagonal Quadratic Forms

This file collects elementary infrastructure for diagonal isotropy statements.
-/

open scoped BigOperators

namespace RatFuncWittLocalGlobal

namespace Diagonal

variable {F K ι : Type*}

/-- Isotropy of the diagonal form with coefficients `a`. -/
def Isotropic [Field F] [Fintype ι] (a : ι → F) : Prop :=
  ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0

/-- The ternary diagonal isotropy predicate in component form. -/
def TernaryIsotropic [Field F] (a₀ a₁ a₂ : F) : Prop :=
  ∃ x₀ x₁ x₂ : F,
    (x₀ ≠ 0 ∨ x₁ ≠ 0 ∨ x₂ ≠ 0) ∧
      a₀ * x₀ ^ 2 + a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2 = 0

/-- A zero diagonal coefficient supplies an isotropic coordinate vector. -/
theorem isotropic_of_zero_coeff [Field F] [Fintype ι] (a : ι → F) {i : ι}
    (hi : a i = 0) :
    Isotropic a := by
  classical
  let x : ι → F := fun j => if j = i then 1 else 0
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have hxi := congr_fun hx i
    simp [x] at hxi
  · calc
      (∑ j, a j * x j ^ 2) = a i * x i ^ 2 := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          simp [x, hji]
        · intro hi_notin
          simp at hi_notin
      _ = 0 := by
        simp [x, hi]

theorem ternary_isotropic_iff_exists_tuple_ne [Field F] {a₀ a₁ a₂ : F} :
    TernaryIsotropic a₀ a₁ a₂ ↔
      ∃ x₀ x₁ x₂ : F,
        (x₀, x₁, x₂) ≠ (0, 0, 0) ∧
          a₀ * x₀ ^ 2 + a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2 = 0 := by
  constructor
  · rintro ⟨x₀, x₁, x₂, hx_ne, hx_sum⟩
    refine ⟨x₀, x₁, x₂, ?_, hx_sum⟩
    intro hx_tuple
    simp only [Prod.mk.injEq] at hx_tuple
    rcases hx_tuple with ⟨hx₀, hx₁, hx₂⟩
    rcases hx_ne with hx₀_ne | hx₁_ne | hx₂_ne
    · exact hx₀_ne hx₀
    · exact hx₁_ne hx₁
    · exact hx₂_ne hx₂
  · rintro ⟨x₀, x₁, x₂, hx_ne, hx_sum⟩
    refine ⟨x₀, x₁, x₂, ?_, hx_sum⟩
    by_contra hx_all
    simp only [not_or, not_not] at hx_all
    exact hx_ne (by simp [hx_all])

theorem isotropic_fin_three_iff [Field F] (a : Fin 3 → F) :
    Isotropic a ↔ TernaryIsotropic (a 0) (a 1) (a 2) := by
  constructor
  · rintro ⟨x, hx_ne, hx_sum⟩
    refine ⟨x 0, x 1, x 2, ?_, ?_⟩
    · by_contra h
      simp only [not_or, not_not] at h
      apply hx_ne
      funext i
      fin_cases i <;> simp [h]
    · simpa [TernaryIsotropic, Fin.sum_univ_three] using hx_sum
  · rintro ⟨x₀, x₁, x₂, hx_ne, hx_sum⟩
    refine ⟨![x₀, x₁, x₂], ?_, ?_⟩
    · intro hx
      rcases hx_ne with hx₀ | hx₁ | hx₂
      · exact hx₀ (by simpa using congr_fun hx 0)
      · exact hx₁ (by simpa using congr_fun hx 1)
      · exact hx₂ (by simpa using congr_fun hx 2)
    · simpa [Isotropic, TernaryIsotropic, Fin.sum_univ_three] using hx_sum

theorem isotropic_comp_equiv [Field F] [Fintype ι] [Fintype J]
    (e : ι ≃ J) (a : J → F) :
    Isotropic (fun i : ι => a (e i)) ↔ Isotropic a := by
  constructor
  · rintro ⟨x, hx_ne, hx_sum⟩
    refine ⟨fun k => x (e.symm k), ?_, ?_⟩
    · intro hx
      apply hx_ne
      funext i
      have hi := congr_fun hx (e i)
      simpa using hi
    · have hsum :
          (∑ k, a k * x (e.symm k) ^ 2) =
            ∑ i, a (e i) * x i ^ 2 := by
        simpa using e.symm.sum_comp (fun i : ι => a (e i) * x i ^ 2)
      exact hsum.trans hx_sum
  · rintro ⟨x, hx_ne, hx_sum⟩
    refine ⟨fun i => x (e i), ?_, ?_⟩
    · intro hx
      apply hx_ne
      funext k
      have hk := congr_fun hx (e.symm k)
      simpa using hk
    · have hsum :
          (∑ i, a (e i) * x (e i) ^ 2) =
            ∑ k, a k * x k ^ 2 := by
        simpa using e.sum_comp (fun k : J => a k * x k ^ 2)
      exact hsum.trans hx_sum

theorem isotropic_mul_square [Field F] [Fintype ι] {a u : ι → F}
    (hu : ∀ i, u i ≠ 0) :
    Isotropic (fun i => a i * u i ^ 2) ↔ Isotropic a := by
  constructor
  · rintro ⟨x, hx_ne, hx_sum⟩
    refine ⟨fun i => x i * u i, ?_, ?_⟩
    · intro hxu
      apply hx_ne
      funext i
      have hi := congr_fun hxu i
      exact mul_eq_zero.mp hi |>.resolve_right (hu i)
    · calc
        ∑ i, a i * (x i * u i) ^ 2
            = ∑ i, (a i * u i ^ 2) * x i ^ 2 := by
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = 0 := hx_sum
  · rintro ⟨x, hx_ne, hx_sum⟩
    refine ⟨fun i => x i / u i, ?_, ?_⟩
    · intro hxu
      apply hx_ne
      funext i
      have hi := congr_fun hxu i
      have := congrArg (fun t => t * u i) hi
      simpa [hu i] using this
    · calc
        ∑ i, (a i * u i ^ 2) * (x i / u i) ^ 2
            = ∑ i, a i * x i ^ 2 := by
                apply Finset.sum_congr rfl
                intro i _
                field_simp [hu i]
        _ = 0 := hx_sum

theorem ternary_isotropic_const_mul [Field F] {a₀ a₁ a₂ c : F}
    (hc : c ≠ 0) :
    TernaryIsotropic (c * a₀) (c * a₁) (c * a₂) ↔
      TernaryIsotropic a₀ a₁ a₂ := by
  constructor
  · rintro ⟨x₀, x₁, x₂, hx_ne, hx_sum⟩
    refine ⟨x₀, x₁, x₂, hx_ne, ?_⟩
    have hmul : c * (a₀ * x₀ ^ 2 + a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2) = 0 := by
      simpa [mul_add, mul_assoc] using hx_sum
    exact (mul_eq_zero.mp hmul).resolve_left hc
  · rintro ⟨x₀, x₁, x₂, hx_ne, hx_sum⟩
    refine ⟨x₀, x₁, x₂, hx_ne, ?_⟩
    calc
      (c * a₀) * x₀ ^ 2 + (c * a₁) * x₁ ^ 2 + (c * a₂) * x₂ ^ 2
          = c * (a₀ * x₀ ^ 2 + a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2) := by
            ring
      _ = 0 := by simp [hx_sum]

theorem ternary_isotropic_mul_square [Field F] {a₀ a₁ a₂ u₀ u₁ u₂ : F}
    (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) :
    TernaryIsotropic (a₀ * u₀ ^ 2) (a₁ * u₁ ^ 2) (a₂ * u₂ ^ 2) ↔
      TernaryIsotropic a₀ a₁ a₂ := by
  constructor
  · rintro ⟨x₀, x₁, x₂, hx_ne, hx_sum⟩
    refine ⟨x₀ * u₀, x₁ * u₁, x₂ * u₂, ?_, ?_⟩
    · rcases hx_ne with hx₀ | hx₁ | hx₂
      · exact Or.inl fun h ↦ hx₀ (mul_eq_zero.mp h |>.resolve_right hu₀)
      · exact Or.inr <| Or.inl fun h ↦ hx₁ (mul_eq_zero.mp h |>.resolve_right hu₁)
      · exact Or.inr <| Or.inr fun h ↦ hx₂ (mul_eq_zero.mp h |>.resolve_right hu₂)
    · calc
        a₀ * (x₀ * u₀) ^ 2 + a₁ * (x₁ * u₁) ^ 2 + a₂ * (x₂ * u₂) ^ 2
            = (a₀ * u₀ ^ 2) * x₀ ^ 2 +
              (a₁ * u₁ ^ 2) * x₁ ^ 2 +
              (a₂ * u₂ ^ 2) * x₂ ^ 2 := by
                ring
        _ = 0 := hx_sum
  · rintro ⟨x₀, x₁, x₂, hx_ne, hx_sum⟩
    refine ⟨x₀ / u₀, x₁ / u₁, x₂ / u₂, ?_, ?_⟩
    · rcases hx_ne with hx₀ | hx₁ | hx₂
      · exact Or.inl fun h ↦ hx₀ (by
          have := congrArg (fun t => t * u₀) h
          simpa [hu₀] using this)
      · exact Or.inr <| Or.inl fun h ↦ hx₁ (by
          have := congrArg (fun t => t * u₁) h
          simpa [hu₁] using this)
      · exact Or.inr <| Or.inr fun h ↦ hx₂ (by
          have := congrArg (fun t => t * u₂) h
          simpa [hu₂] using this)
    · calc
        (a₀ * u₀ ^ 2) * (x₀ / u₀) ^ 2 +
          (a₁ * u₁ ^ 2) * (x₁ / u₁) ^ 2 +
          (a₂ * u₂ ^ 2) * (x₂ / u₂) ^ 2
            = a₀ * x₀ ^ 2 + a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2 := by
                field_simp [hu₀, hu₁, hu₂]
        _ = 0 := hx_sum

theorem ternary_isotropic_one_of_isSquare_neg_left [Field F] {b c : F}
    (hb : IsSquare (-b)) :
    TernaryIsotropic 1 b c := by
  rcases hb with ⟨r, hr⟩
  refine ⟨r, 1, 0, Or.inr (Or.inl one_ne_zero), ?_⟩
  have hrpow : r ^ 2 = -b := by
    simpa [pow_two] using hr.symm
  calc
    1 * r ^ 2 + b * 1 ^ 2 + c * 0 ^ 2 = r ^ 2 + b := by ring
    _ = 0 := by
      rw [hrpow]
      ring

theorem ternary_isotropic_one_of_isSquare_neg_right [Field F] {b c : F}
    (hc : IsSquare (-c)) :
    TernaryIsotropic 1 b c := by
  rcases hc with ⟨r, hr⟩
  refine ⟨r, 0, 1, Or.inr (Or.inr one_ne_zero), ?_⟩
  have hrpow : r ^ 2 = -c := by
    simpa [pow_two] using hr.symm
  calc
    1 * r ^ 2 + b * 0 ^ 2 + c * 1 ^ 2 = r ^ 2 + c := by ring
    _ = 0 := by
      rw [hrpow]
      ring

theorem ternary_isotropic_one_iff_binary_or_isSquare_neg_right [Field F] {b c : F} :
    TernaryIsotropic 1 b c ↔
      (∃ y z : F, y ^ 2 + c * z ^ 2 = -b) ∨ IsSquare (-c) := by
  constructor
  · rintro ⟨x₀, x₁, x₂, hx_ne, hx_sum⟩
    by_cases hx₁ : x₁ = 0
    · right
      have hx₂ : x₂ ≠ 0 := by
        intro hx₂
        rcases hx_ne with hx₀ | hx₁_ne | hx₂_ne
        · have hx₀_sq : x₀ ^ 2 = 0 := by
            simpa [hx₁, hx₂] using hx_sum
          exact hx₀ (sq_eq_zero_iff.mp hx₀_sq)
        · exact hx₁_ne hx₁
        · exact hx₂_ne hx₂
      refine ⟨x₀ / x₂, ?_⟩
      have hsum : x₀ ^ 2 + c * x₂ ^ 2 = 0 := by
        simpa [hx₁] using hx_sum
      have hdiv : x₀ ^ 2 / x₂ ^ 2 + c = 0 := by
        field_simp [hx₂]
        simpa [add_comm, mul_comm] using hsum
      have hc_eq : -c = x₀ ^ 2 / x₂ ^ 2 := by
        exact (eq_neg_of_add_eq_zero_left hdiv).symm
      calc
        -c = x₀ ^ 2 / x₂ ^ 2 := hc_eq
        _ = (x₀ / x₂) * (x₀ / x₂) := by
          field_simp [hx₂]
    · left
      refine ⟨x₀ / x₁, x₂ / x₁, ?_⟩
      have hsum : x₀ ^ 2 + b * x₁ ^ 2 + c * x₂ ^ 2 = 0 := by
        simpa using hx_sum
      have hdiv : x₀ ^ 2 / x₁ ^ 2 + b + c * (x₂ ^ 2 / x₁ ^ 2) = 0 := by
        field_simp [hx₁]
        simpa [add_comm, add_left_comm, add_assoc, mul_add, mul_comm, mul_left_comm,
          mul_assoc] using hsum
      have hb_eq : x₀ ^ 2 / x₁ ^ 2 + c * (x₂ ^ 2 / x₁ ^ 2) = -b := by
        rw [← add_eq_zero_iff_eq_neg]
        simpa [add_comm, add_left_comm, add_assoc] using hdiv
      calc
        (x₀ / x₁) ^ 2 + c * (x₂ / x₁) ^ 2 =
            x₀ ^ 2 / x₁ ^ 2 + c * (x₂ ^ 2 / x₁ ^ 2) := by
              field_simp [hx₁]
        _ = -b := hb_eq
  · rintro (⟨y, z, hyz⟩ | hc)
    · refine ⟨y, 1, z, Or.inr (Or.inl one_ne_zero), ?_⟩
      calc
        1 * y ^ 2 + b * 1 ^ 2 + c * z ^ 2 = y ^ 2 + c * z ^ 2 + b := by ring
        _ = 0 := by
          rw [hyz]
          ring
    · exact ternary_isotropic_one_of_isSquare_neg_right hc

theorem ternary_isotropic_normalize_first [Field F] {a₀ a₁ a₂ : F}
    (ha₀ : a₀ ≠ 0) :
    TernaryIsotropic 1 (a₁ / a₀) (a₂ / a₀) ↔
      TernaryIsotropic a₀ a₁ a₂ := by
  simpa [div_eq_mul_inv, inv_mul_cancel₀ ha₀, mul_comm, mul_left_comm, mul_assoc] using
    (ternary_isotropic_const_mul (F := F) (a₀ := a₀) (a₁ := a₁) (a₂ := a₂)
      (c := a₀⁻¹) (inv_ne_zero ha₀))

theorem isotropic_baseChange [Field F] [Field K] [Algebra F K] [Fintype ι]
    {a : ι → F} (h : Isotropic a) :
    ∃ x : ι → K,
      x ≠ 0 ∧ ∑ i, algebraMap F K (a i) * x i ^ 2 = 0 := by
  rcases h with ⟨x, hx_ne, hx_sum⟩
  refine ⟨fun i => algebraMap F K (x i), ?_, ?_⟩
  · intro hx_map
    apply hx_ne
    funext i
    exact (algebraMap F K).injective (by simpa using congr_fun hx_map i)
  · calc
      ∑ i, algebraMap F K (a i) * algebraMap F K (x i) ^ 2
          = ∑ i, algebraMap F K (a i * x i ^ 2) := by
              simp [map_mul, map_pow]
      _ = algebraMap F K (∑ i, a i * x i ^ 2) := by
              simp [map_sum]
      _ = 0 := by
              simp [hx_sum]

end Diagonal

namespace RatFunc

variable {R ι : Type*}

def TernaryLocallyIsotropic
    [Field R] (a₀ a₁ a₂ : RatFunc R) : Prop :=
  ∀ {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
    [Algebra (RatFunc R) K],
    Diagonal.TernaryIsotropic
      (algebraMap (RatFunc R) K a₀)
      (algebraMap (RatFunc R) K a₁)
      (algebraMap (RatFunc R) K a₂)

universe u v
theorem ternary_locally_isotropic_const_mul
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a₀ a₁ a₂ c : RatFunc R} (hc : c ≠ 0) :
    TernaryLocallyIsotropic.{u, v} (c * a₀) (c * a₁) (c * a₂) ↔
      TernaryLocallyIsotropic.{u, v} a₀ a₁ a₂ := by
  constructor
  · intro h K _ _ _ _ _
    have hK :
        Diagonal.TernaryIsotropic
          (algebraMap (RatFunc R) K (c * a₀))
          (algebraMap (RatFunc R) K (c * a₁))
          (algebraMap (RatFunc R) K (c * a₂)) := h
    have hK' :
        Diagonal.TernaryIsotropic
          (algebraMap (RatFunc R) K c * algebraMap (RatFunc R) K a₀)
          (algebraMap (RatFunc R) K c * algebraMap (RatFunc R) K a₁)
          (algebraMap (RatFunc R) K c * algebraMap (RatFunc R) K a₂) := by
      simpa [map_mul] using hK
    have hcK : algebraMap (RatFunc R) K c ≠ 0 :=
      by simpa using (algebraMap (RatFunc R) K).injective.ne hc
    exact
      (Diagonal.ternary_isotropic_const_mul (F := K)
        (a₀ := algebraMap (RatFunc R) K a₀)
        (a₁ := algebraMap (RatFunc R) K a₁)
        (a₂ := algebraMap (RatFunc R) K a₂)
        (c := algebraMap (RatFunc R) K c) hcK).mp hK'
  · intro h K _ _ _ _ _
    have hK :
        Diagonal.TernaryIsotropic
          (algebraMap (RatFunc R) K a₀)
          (algebraMap (RatFunc R) K a₁)
          (algebraMap (RatFunc R) K a₂) := h
    have hcK : algebraMap (RatFunc R) K c ≠ 0 :=
      by simpa using (algebraMap (RatFunc R) K).injective.ne hc
    simpa [map_mul] using
      (Diagonal.ternary_isotropic_const_mul (F := K)
        (a₀ := algebraMap (RatFunc R) K a₀)
        (a₁ := algebraMap (RatFunc R) K a₁)
        (a₂ := algebraMap (RatFunc R) K a₂)
        (c := algebraMap (RatFunc R) K c) hcK).mpr hK

theorem ternary_locally_isotropic_normalize_first
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a₀ a₁ a₂ : RatFunc R} (ha₀ : a₀ ≠ 0) :
    TernaryLocallyIsotropic.{u, v} 1 (a₁ / a₀) (a₂ / a₀) ↔
      TernaryLocallyIsotropic.{u, v} a₀ a₁ a₂ := by
  simpa [div_eq_mul_inv, inv_mul_cancel₀ ha₀, mul_comm, mul_left_comm, mul_assoc] using
    (ternary_locally_isotropic_const_mul (R := R)
      (a₀ := a₀) (a₁ := a₁) (a₂ := a₂) (c := a₀⁻¹) (inv_ne_zero ha₀))

end RatFunc

end RatFuncWittLocalGlobal
