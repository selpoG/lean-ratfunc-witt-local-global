/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.RealClosure.Intermediate

/-!
# Odd irreducible factors and odd power bases

An odd-degree polynomial has an odd-degree irreducible factor.  Once such a
factor is chosen, a root in the algebraic closure is integral and its simple
intermediate field has a power basis whose dimension is the degree of that
factor.  This file packages those elementary pieces for the odd-root branch
of the ordered-closure argument.
-/

namespace RatFuncWittLocalGlobal

open Polynomial

/-!
### Odd-degree irreducible factors
-/

/-- Every odd-degree polynomial over a field has a monic irreducible odd-degree factor. -/
theorem Polynomial.exists_odd_natDegree_monic_irreducible_factor
    {K : Type*} [Field K] {p : K[X]} (hp : Odd p.natDegree) :
    ∃ q : K[X], Odd q.natDegree ∧ q.Monic ∧ Irreducible q ∧ q ∣ p := by
  have hmain : ∀ n : ℕ, ∀ p : K[X], p.natDegree = n → Odd n →
      ∃ q : K[X], Odd q.natDegree ∧ q.Monic ∧ Irreducible q ∧ q ∣ p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hpdeg hpodd
      have hnpos : 0 < n := hpodd.pos
      have hp0 : p ≠ 0 := by
        intro hpzero
        apply (Nat.ne_of_gt hnpos)
        simpa [hpzero] using hpdeg.symm
      have hpunit : ¬ IsUnit p := by
        exact Polynomial.not_isUnit_of_natDegree_pos p (hpdeg ▸ hnpos)
      obtain ⟨q, hqmonic, hqirr, hqdiv⟩ :=
        Polynomial.exists_monic_irreducible_factor p hpunit
      obtain ⟨r, hpr⟩ := (dvd_iff_exists_eq_mul_right.mp hqdiv)
      have hq0 : q ≠ 0 := hqirr.ne_zero
      have hr0 : r ≠ 0 := by
        intro hr
        apply hp0
        rw [hpr, hr, mul_zero]
      have hdeg : n = q.natDegree + r.natDegree := by
        calc
          n = p.natDegree := hpdeg.symm
          _ = (q * r).natDegree := by rw [hpr]
          _ = q.natDegree + r.natDegree := natDegree_mul hq0 hr0
      by_cases hqodd : Odd q.natDegree
      · exact ⟨q, hqodd, hqmonic, hqirr, hqdiv⟩
      · have hqeven : Even q.natDegree := (Nat.not_odd_iff_even).mp hqodd
        have hrodd : Odd r.natDegree := by
          apply (Nat.not_even_iff_odd).mp
          intro hreven
          apply (Nat.not_even_iff_odd).mpr hpodd
          rw [hdeg]
          exact hqeven.add hreven
        have hqpos : 0 < q.natDegree := hqirr.natDegree_pos
        have hrlt : r.natDegree < n := by
          rw [hdeg]
          exact Nat.lt_add_of_pos_left hqpos
        obtain ⟨s, hsodd, hsmonic, hsirr, hsdiv⟩ :=
          ih r.natDegree hrlt r rfl hrodd
        have hrdvp : r ∣ p := by
          rw [hpr]
          rw [mul_comm]
          exact dvd_mul_right r q
        exact ⟨s, hsodd, hsmonic, hsirr, hsdiv.trans hrdvp⟩
  exact hmain p.natDegree p rfl hp

namespace OrderedRealClosure

universe u

/-!
### Minimal polynomial and odd root power basis
-/

/-- A monic irreducible annihilator is the minimal polynomial. -/
theorem minpoly_eq_of_monic_irreducible_root
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {q : K[X]} {α : L} (hqmonic : q.Monic) (hqirr : Irreducible q)
    (hroot : Polynomial.aeval α q = 0) : minpoly K α = q := by
  exact (minpoly.eq_of_irreducible_of_monic hqirr hroot hqmonic).symm

end OrderedRealClosure
end RatFuncWittLocalGlobal
