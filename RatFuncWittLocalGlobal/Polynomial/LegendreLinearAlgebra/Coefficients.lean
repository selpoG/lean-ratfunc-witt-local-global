/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Polynomial coefficient lemmas used by the Legendre argument

This module contains only the bounded-degree and top-coefficient facts used by
the public ternary proof.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u

theorem polynomial_natDegree_lt_of_mem_degreeLT
    {R : Type u} [Semiring R] {n : ℕ} {p : Polynomial R}
    (hp : p ∈ Polynomial.degreeLT R n) (hp0 : p ≠ 0) :
    p.natDegree < n := by
  have hdeg := Polynomial.mem_degreeLT.mp hp
  rwa [Polynomial.degree_eq_natDegree hp0, Nat.cast_lt] at hdeg

theorem polynomial_coeff_mul_eq_coeff_mul_of_natDegree_eq
    {R : Type u} [Semiring R] {m n : ℕ} {p q : Polynomial R}
    (hp : p.natDegree = m) (hq : q.natDegree = n) :
    (p * q).coeff (m + n) = p.coeff m * q.coeff n := by
  simpa [Polynomial.leadingCoeff, hp, hq] using
    Polynomial.coeff_mul_degree_add_degree p q

theorem polynomial_coeff_sq_natDegree_mul_two
    {R : Type u} [Semiring R] {p : Polynomial R} :
    (p ^ 2).coeff (2 * p.natDegree) = p.leadingCoeff ^ 2 := by
  have hmul :=
    polynomial_coeff_mul_eq_coeff_mul_of_natDegree_eq
      (p := p) (q := p) rfl rfl
  simp [pow_two, two_mul] at hmul ⊢

theorem polynomial_coeff_sq_natDegree_mul_two_at
    {R : Type u} [Semiring R] {p : Polynomial R} {k : ℕ}
    (hk : 2 * p.natDegree = k) :
    (p ^ 2).coeff k = p.leadingCoeff ^ 2 := by
  subst k
  exact polynomial_coeff_sq_natDegree_mul_two

theorem polynomial_coeff_sq_add_mul_of_top_degrees
    {R : Type u} [Semiring R] {u B C : Polynomial R} {k : ℕ}
    (hu : 2 * u.natDegree = k)
    (hBC : B.natDegree + C.natDegree = k) :
    (u ^ 2 + B * C).coeff k =
      u.leadingCoeff ^ 2 + B.leadingCoeff * C.leadingCoeff := by
  rw [Polynomial.coeff_add]
  rw [polynomial_coeff_sq_natDegree_mul_two_at hu]
  rw [← hBC]
  rw [polynomial_coeff_mul_eq_coeff_mul_of_natDegree_eq (p := B) (q := C) rfl rfl]
  rw [Polynomial.coeff_natDegree, Polynomial.coeff_natDegree]

end RatFunc
end RatFuncWittLocalGlobal
