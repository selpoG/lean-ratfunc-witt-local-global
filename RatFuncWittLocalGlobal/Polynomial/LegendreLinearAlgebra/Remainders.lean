/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Polynomial.LegendreLinearAlgebra.Coefficients
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Bounded polynomial remainder representatives

The public proof needs only the linear remainder map for a nonzero divisor and
the divisibility facts relating a polynomial to its bounded representative.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u

noncomputable def modByNonzeroDegreeLTLinearMap
    {R : Type u} [Field R] (q : Polynomial R) (hq0 : q ≠ 0) :
    Polynomial R →ₗ[R] Polynomial.degreeLT R q.natDegree :=
  (Polynomial.modByMonicHom (q * Polynomial.C q.leadingCoeff⁻¹)).codRestrict
    (Polynomial.degreeLT R q.natDegree) fun p => by
      exact Polynomial.mem_degreeLT.mpr (by
        simpa [Polynomial.degree_mul_leadingCoeff_inv q hq0,
          Polynomial.degree_eq_natDegree hq0] using
            Polynomial.degree_modByMonic_lt p
              (Polynomial.monic_mul_leadingCoeff_inv hq0))

theorem associated_mul_leadingCoeff_inv
    {R : Type u} [Field R] {q : Polynomial R} (hq0 : q ≠ 0) :
    Associated (q * Polynomial.C q.leadingCoeff⁻¹) q := by
  refine associated_of_dvd_dvd ?_ ?_
  · refine ⟨Polynomial.C q.leadingCoeff, ?_⟩
    rw [mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ (mt Polynomial.leadingCoeff_eq_zero.1 hq0),
      Polynomial.C_1, mul_one]
  · exact dvd_mul_right q (Polynomial.C q.leadingCoeff⁻¹)

theorem dvd_sub_modByNonzeroDegreeLTLinearMap
    {R : Type u} [Field R] {q p : Polynomial R} (hq0 : q ≠ 0) :
    q ∣ p - (modByNonzeroDegreeLTLinearMap q hq0 p : Polynomial R) := by
  let m := q * Polynomial.C q.leadingCoeff⁻¹
  have hmdiv : m ∣ p - p %ₘ m := by
    refine ⟨p /ₘ m, ?_⟩
    have h := Polynomial.modByMonic_add_div p m
    calc
      p - p %ₘ m = (p %ₘ m + m * (p /ₘ m)) - p %ₘ m := by rw [h]
      _ = m * (p /ₘ m) := by ring
  change q ∣ p - p %ₘ m
  exact ((associated_mul_leadingCoeff_inv hq0).dvd_iff_dvd_left).mp hmdiv

theorem dvd_square_add_of_modByNonzeroDegreeLTLinearMap
    {R : Type u} [Field R] {q u t : Polynomial R} (hq0 : q ≠ 0)
    (h : q ∣ u ^ 2 + t) :
    q ∣ (modByNonzeroDegreeLTLinearMap q hq0 u : Polynomial R) ^ 2 + t := by
  let r : Polynomial R := modByNonzeroDegreeLTLinearMap q hq0 u
  have hsub : q ∣ u - r := dvd_sub_modByNonzeroDegreeLTLinearMap hq0
  have hsq : q ∣ u ^ 2 - r ^ 2 := by
    rw [sq_sub_sq]
    exact dvd_mul_of_dvd_right hsub (u + r)
  have htarget : r ^ 2 + t = (u ^ 2 + t) - (u ^ 2 - r ^ 2) := by ring
  rw [htarget]
  exact dvd_sub h hsq

end RatFunc

end RatFuncWittLocalGlobal
