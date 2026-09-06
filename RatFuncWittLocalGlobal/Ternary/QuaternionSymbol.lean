/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Core.Diagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Quaternion Symbol Split Predicate

This file contains the lightweight conic predicate used for the quaternion-symbol
route to ternary local-global.  It deliberately avoids introducing quaternion
algebras or Brauer groups at this layer.
-/

namespace RatFuncWittLocalGlobal

variable {F : Type*}

/--
The conic attached to the quaternion symbol `(u, v)` has a nontrivial point.

With this convention, `QuaternionSymbolSplit (-b) (-c)` is definitionally the
same conic as the normalized ternary form `⟨1, b, c⟩`.
-/
def QuaternionSymbolSplit [Field F] (u v : F) : Prop :=
  ∃ x y z : F,
    (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x ^ 2 - u * y ^ 2 - v * z ^ 2 = 0

/-- A split quaternion-symbol conic remains split after base change. -/
theorem quaternionSymbolSplit_baseChange [Field F] [Field K] [Algebra F K] {u v : F}
    (h : QuaternionSymbolSplit u v) :
    QuaternionSymbolSplit (algebraMap F K u) (algebraMap F K v) := by
  rcases h with ⟨x, y, z, hne, hsum⟩
  refine ⟨algebraMap F K x, algebraMap F K y, algebraMap F K z, ?_, ?_⟩
  · rcases hne with hx | hy | hz
    · exact Or.inl (fun hzero => hx ((algebraMap F K).injective (by simpa using hzero)))
    · exact Or.inr (Or.inl
        (fun hzero => hy ((algebraMap F K).injective (by simpa using hzero))))
    · exact Or.inr (Or.inr
        (fun hzero => hz ((algebraMap F K).injective (by simpa using hzero))))
  · have hmap := congrArg (algebraMap F K) hsum
    simpa using hmap

/-- The quaternion-symbol split predicate is symmetric in its two coefficients. -/
theorem quaternionSymbolSplit_comm [Field F] {u v : F} :
    QuaternionSymbolSplit u v ↔ QuaternionSymbolSplit v u := by
  constructor
  · rintro ⟨x, y, z, hne, hsum⟩
    refine ⟨x, z, y, ?_, ?_⟩
    · rcases hne with hx | hy | hz
      · exact Or.inl hx
      · exact Or.inr (Or.inr hy)
      · exact Or.inr (Or.inl hz)
    · calc
        x ^ 2 - v * z ^ 2 - u * y ^ 2 =
            x ^ 2 - u * y ^ 2 - v * z ^ 2 := by ring
        _ = 0 := hsum
  · rintro ⟨x, z, y, hne, hsum⟩
    refine ⟨x, y, z, ?_, ?_⟩
    · rcases hne with hx | hz | hy
      · exact Or.inl hx
      · exact Or.inr (Or.inr hz)
      · exact Or.inr (Or.inl hy)
    · calc
        x ^ 2 - u * y ^ 2 - v * z ^ 2 =
            x ^ 2 - v * z ^ 2 - u * y ^ 2 := by ring
        _ = 0 := hsum

/-- If the first quaternion-symbol coefficient is a square, the symbol is split. -/
theorem quaternionSymbolSplit_of_isSquare_left [Field F] {u v : F} (hu : IsSquare u) :
    QuaternionSymbolSplit u v := by
  rcases hu with ⟨s, rfl⟩
  refine ⟨s, 1, 0, Or.inr (Or.inl one_ne_zero), ?_⟩
  ring

/-- If the second quaternion-symbol coefficient is a square, the symbol is split. -/
theorem quaternionSymbolSplit_of_isSquare_right [Field F] {u v : F} (hv : IsSquare v) :
    QuaternionSymbolSplit u v := by
  exact quaternionSymbolSplit_comm.mpr (quaternionSymbolSplit_of_isSquare_left hv)

/-- If the second quaternion-symbol coefficient is zero, the symbol is split. -/
theorem quaternionSymbolSplit_of_right_eq_zero [Field F] {u v : F} (hv : v = 0) :
    QuaternionSymbolSplit u v := by
  subst v
  exact quaternionSymbolSplit_of_isSquare_right IsSquare.zero

/--
Multiplying the first quaternion-symbol coefficient by a nonzero square does
not change splitness.
-/
theorem quaternionSymbolSplit_mul_square_left [Field F] {u v s : F} (hs : s ≠ 0) :
    QuaternionSymbolSplit (u * s ^ 2) v ↔ QuaternionSymbolSplit u v := by
  constructor
  · rintro ⟨x, y, z, hne, hsum⟩
    refine ⟨x, s * y, z, ?_, ?_⟩
    · rcases hne with hx | hy | hz
      · exact Or.inl hx
      · exact Or.inr (Or.inl (mul_ne_zero hs hy))
      · exact Or.inr (Or.inr hz)
    · calc
        x ^ 2 - u * (s * y) ^ 2 - v * z ^ 2 =
            x ^ 2 - (u * s ^ 2) * y ^ 2 - v * z ^ 2 := by ring
        _ = 0 := hsum
  · rintro ⟨x, y, z, hne, hsum⟩
    refine ⟨x, y / s, z, ?_, ?_⟩
    · rcases hne with hx | hy | hz
      · exact Or.inl hx
      · exact Or.inr (Or.inl (div_ne_zero hy hs))
      · exact Or.inr (Or.inr hz)
    · calc
        x ^ 2 - (u * s ^ 2) * (y / s) ^ 2 - v * z ^ 2 =
            x ^ 2 - u * y ^ 2 - v * z ^ 2 := by
              field_simp [hs]
        _ = 0 := hsum

/--
Multiplying the second quaternion-symbol coefficient by a nonzero square does
not change splitness.
-/
theorem quaternionSymbolSplit_mul_square_right [Field F] {u v s : F} (hs : s ≠ 0) :
    QuaternionSymbolSplit u (v * s ^ 2) ↔ QuaternionSymbolSplit u v := by
  calc
    QuaternionSymbolSplit u (v * s ^ 2) ↔ QuaternionSymbolSplit (v * s ^ 2) u :=
      quaternionSymbolSplit_comm
    _ ↔ QuaternionSymbolSplit v u :=
      quaternionSymbolSplit_mul_square_left hs
    _ ↔ QuaternionSymbolSplit u v :=
      quaternionSymbolSplit_comm

/--
The conic split condition for `(u, v)` is equivalently a quadratic-algebra norm
equation in `F[√u]`, with the square factor on the `v` side kept explicit.
-/
theorem quaternionSymbolSplit_iff_quadraticAlgebra_norm [Field F] {u v : F} :
    QuaternionSymbolSplit u v ↔
      ∃ x y z : F,
        (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
          QuadraticAlgebra.norm (⟨x, y⟩ : QuadraticAlgebra F u 0) = v * z ^ 2 := by
  constructor
  · rintro ⟨x, y, z, hne, hsum⟩
    refine ⟨x, y, z, hne, ?_⟩
    calc
      QuadraticAlgebra.norm (⟨x, y⟩ : QuadraticAlgebra F u 0) =
          x ^ 2 - u * y ^ 2 := by
            simp [QuadraticAlgebra.norm_def, pow_two]
            ring
      _ = v * z ^ 2 := sub_eq_zero.mp hsum
  · rintro ⟨x, y, z, hne, hnorm⟩
    refine ⟨x, y, z, hne, ?_⟩
    have hnorm' : x ^ 2 - u * y ^ 2 = v * z ^ 2 := by
      calc
        x ^ 2 - u * y ^ 2 = x * x - u * y * y := by ring
        _ = v * z ^ 2 := by
          simpa [QuadraticAlgebra.norm_def, pow_two] using hnorm
    rw [hnorm', sub_self]

/--
Multiplying the second quaternion-symbol coefficient by a nonzero norm from
`F[√u]` preserves splitness in the forward direction.
-/
theorem quaternionSymbolSplit_mul_norm_right [Field F] {u v n α β : F}
    (hn : n = α ^ 2 - u * β ^ 2) (hn0 : n ≠ 0) :
    QuaternionSymbolSplit u v → QuaternionSymbolSplit u (v * n) := by
  intro hsplit
  rcases (quaternionSymbolSplit_iff_quadraticAlgebra_norm.mp hsplit) with
    ⟨x, y, z, hne, hnorm⟩
  let e : QuadraticAlgebra F u 0 := ⟨x, y⟩
  let w : QuadraticAlgebra F u 0 := ⟨α, β⟩
  have hw_norm_eq : QuadraticAlgebra.norm w = n := by
    rw [hn]
    simp [w, QuadraticAlgebra.norm_def, pow_two]
    ring
  refine quaternionSymbolSplit_iff_quadraticAlgebra_norm.mpr ?_
  refine ⟨(e * w).re, (e * w).im, z, ?_, ?_⟩
  · by_cases hz : z = 0
    · have he_ne : e ≠ 0 := by
        intro he
        rcases hne with hx | hy | hz'
        · exact hx (by simpa [e, QuadraticAlgebra.ext_iff] using congrArg QuadraticAlgebra.re he)
        · exact hy (by simpa [e, QuadraticAlgebra.ext_iff] using congrArg QuadraticAlgebra.im he)
        · exact hz' hz
      have hw_norm_ne : QuadraticAlgebra.norm w ≠ 0 := by
        intro hw0
        exact hn0 (by rw [← hw_norm_eq]; exact hw0)
      have hw_nzd : w ∈ nonZeroDivisors (QuadraticAlgebra F u 0) :=
        (QuadraticAlgebra.norm_mem_nonZeroDivisors_iff).mp
          (mem_nonZeroDivisors_iff_ne_zero.mpr hw_norm_ne)
      by_contra hprod_ne
      push Not at hprod_ne
      have hprod_zero : e * w = 0 := by
        ext <;> simp [hprod_ne.1, hprod_ne.2]
      exact he_ne ((mem_nonZeroDivisors_iff_right.mp hw_nzd) e hprod_zero)
    · exact Or.inr (Or.inr hz)
  · calc
      QuadraticAlgebra.norm (⟨(e * w).re, (e * w).im⟩ : QuadraticAlgebra F u 0) =
          QuadraticAlgebra.norm (e * w) := by rfl
      _ = QuadraticAlgebra.norm e * QuadraticAlgebra.norm w := by simp
      _ = (v * z ^ 2) * n := by
        rw [hnorm]
        rw [hw_norm_eq]
      _ = (v * n) * z ^ 2 := by ring

/--
Multiplying the second quaternion-symbol coefficient by a nonzero norm from
`F[√u]` does not change splitness.
-/
theorem quaternionSymbolSplit_mul_norm_right_iff [Field F] {u v n α β : F}
    (hn : n = α ^ 2 - u * β ^ 2) (hn0 : n ≠ 0) :
    QuaternionSymbolSplit u (v * n) ↔ QuaternionSymbolSplit u v := by
  constructor
  · intro hsplit
    have hinv : n⁻¹ = (α / n) ^ 2 - u * (β / n) ^ 2 := by
      field_simp [hn0]
      rw [hn]
    have hsplit' :=
      quaternionSymbolSplit_mul_norm_right (u := u) (v := v * n) (n := n⁻¹)
        (α := α / n) (β := β / n) hinv (inv_ne_zero hn0) hsplit
    simpa [mul_assoc, hn0] using hsplit'
  · exact quaternionSymbolSplit_mul_norm_right hn hn0

/--
Multiplying the first quaternion-symbol coefficient by a nonzero norm from
`F[√v]` does not change splitness.
-/
theorem quaternionSymbolSplit_mul_norm_left_iff [Field F] {u v n α β : F}
    (hn : n = α ^ 2 - v * β ^ 2) (hn0 : n ≠ 0) :
    QuaternionSymbolSplit (u * n) v ↔ QuaternionSymbolSplit u v := by
  calc
    QuaternionSymbolSplit (u * n) v ↔ QuaternionSymbolSplit v (u * n) :=
      quaternionSymbolSplit_comm
    _ ↔ QuaternionSymbolSplit v u :=
      quaternionSymbolSplit_mul_norm_right_iff hn hn0
    _ ↔ QuaternionSymbolSplit u v :=
      quaternionSymbolSplit_comm

namespace Diagonal
/--
The normalized ternary form `⟨1, b, c⟩` is isotropic exactly when the conic for
the quaternion symbol `(-b, -c)` has a nontrivial point.
-/
theorem ternary_isotropic_one_iff_quaternionSymbolSplit [Field F] {b c : F} :
    TernaryIsotropic 1 b c ↔ QuaternionSymbolSplit (-b) (-c) := by
  constructor
  · rintro ⟨x, y, z, hne, hsum⟩
    refine ⟨x, y, z, hne, ?_⟩
    calc
      x ^ 2 - (-b) * y ^ 2 - (-c) * z ^ 2 =
          1 * x ^ 2 + b * y ^ 2 + c * z ^ 2 := by
            ring
      _ = 0 := hsum
  · rintro ⟨x, y, z, hne, hsplit⟩
    refine ⟨x, y, z, hne, ?_⟩
    calc
      1 * x ^ 2 + b * y ^ 2 + c * z ^ 2 =
          x ^ 2 - (-b) * y ^ 2 - (-c) * z ^ 2 := by
            ring
      _ = 0 := hsplit

/--
After normalizing by the first nonzero coefficient, a ternary form is isotropic
exactly when the corresponding quaternion-symbol conic is split.
-/
theorem ternary_isotropic_iff_quaternionSymbolSplit_normalize_first [Field F]
    {a₀ a₁ a₂ : F} (ha₀ : a₀ ≠ 0) :
    TernaryIsotropic a₀ a₁ a₂ ↔
      QuaternionSymbolSplit (-(a₁ / a₀)) (-(a₂ / a₀)) := by
  calc
    TernaryIsotropic a₀ a₁ a₂ ↔ TernaryIsotropic 1 (a₁ / a₀) (a₂ / a₀) :=
      (ternary_isotropic_normalize_first ha₀).symm
    _ ↔ QuaternionSymbolSplit (-(a₁ / a₀)) (-(a₂ / a₀)) :=
      ternary_isotropic_one_iff_quaternionSymbolSplit

end Diagonal

end RatFuncWittLocalGlobal
