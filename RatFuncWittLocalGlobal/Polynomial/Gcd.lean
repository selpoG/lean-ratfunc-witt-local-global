/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Polynomial.Mod
import RatFuncWittLocalGlobal.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.Polynomial.Radical

/-!
# Squarefree gcd decompositions for polynomial coefficients
-/

namespace RatFuncWittLocalGlobal

open UniqueFactorizationMonoid

universe u

/--
The squarefree decomposition attached to two squarefree polynomial
coefficients.  For `G = gcd B C`, it records
`B = G * B₁`, `C = G * C₁`, and the pairwise relative primality needed for
the polynomial Legendre step.
-/
structure SquarefreeGcdSplit {R : Type u} [Field R] (B C : Polynomial R) where
  G : Polynomial R
  B₁ : Polynomial R
  C₁ : Polynomial R
  G_ne_zero : G ≠ 0
  B₁_ne_zero : B₁ ≠ 0
  C₁_ne_zero : C₁ ≠ 0
  hB : B = G * B₁
  hC : C = G * C₁
  squarefree_G : Squarefree G
  squarefree_B₁ : Squarefree B₁
  squarefree_C₁ : Squarefree C₁
  relPrime_G_B₁ : IsRelPrime G B₁
  relPrime_G_C₁ : IsRelPrime G C₁
  relPrime_B₁_C₁ : IsRelPrime B₁ C₁

namespace SquarefreeGcdSplit

variable {R : Type u} [Field R] {B C : Polynomial R} (s : SquarefreeGcdSplit B C)

theorem coprime_G_B₁ : IsCoprime s.G s.B₁ :=
  s.relPrime_G_B₁.isCoprime

theorem coprime_G_C₁ : IsCoprime s.G s.C₁ :=
  s.relPrime_G_C₁.isCoprime

theorem coprime_B₁_C₁ : IsCoprime s.B₁ s.C₁ :=
  s.relPrime_B₁_C₁.isCoprime

theorem isRoot_B_of_irreducible_dvd_B₁_of_linear
    {π : Polynomial R} {a : R}
    (_hπ : Irreducible π) (hπB₁ : π ∣ s.B₁)
    (hlin : Associated π (Polynomial.X - Polynomial.C a)) :
    B.IsRoot a := by
  rw [Polynomial.IsRoot, s.hB, Polynomial.eval_mul]
  have hlinear : Polynomial.X - Polynomial.C a ∣ s.B₁ :=
    hlin.dvd'.trans hπB₁
  have hroot : s.B₁.IsRoot a := Polynomial.dvd_iff_isRoot.mp hlinear
  simp [Polynomial.IsRoot] at hroot
  simp [hroot]

theorem isRoot_C_of_irreducible_dvd_C₁_of_linear
    {π : Polynomial R} {a : R}
    (_hπ : Irreducible π) (hπC₁ : π ∣ s.C₁)
    (hlin : Associated π (Polynomial.X - Polynomial.C a)) :
    C.IsRoot a := by
  rw [Polynomial.IsRoot, s.hC, Polynomial.eval_mul]
  have hlinear : Polynomial.X - Polynomial.C a ∣ s.C₁ :=
    hlin.dvd'.trans hπC₁
  have hroot : s.C₁.IsRoot a := Polynomial.dvd_iff_isRoot.mp hlinear
  simp [Polynomial.IsRoot] at hroot
  simp [hroot]

theorem isSquareMod_neg_C₁_mul_B₁_of_irreducible_dvd_G_of_linear_of_nonneg_eval
    [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {π : Polynomial R} {a : R}
    (_hπ : Irreducible π) (_hπG : π ∣ s.G)
    (hlin : Associated π (Polynomial.X - Polynomial.C a))
    (hnonneg : 0 ≤ (-(s.C₁ * s.B₁)).eval a) :
    IsSquareMod π (-(s.C₁ * s.B₁)) :=
  isSquareMod_linear_associated_of_nonneg_eval hlin hnonneg

theorem isSquareMod_neg_B_of_irreducible_dvd_C₁_of_linear_of_nonneg_eval
    [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {π : Polynomial R} {a : R}
    (_hπ : Irreducible π) (_hπC₁ : π ∣ s.C₁)
    (hlin : Associated π (Polynomial.X - Polynomial.C a))
    (hnonneg : 0 ≤ (-B).eval a) :
    IsSquareMod π (-B) :=
  isSquareMod_linear_associated_of_nonneg_eval hlin hnonneg

theorem isSquareMod_neg_C_of_irreducible_dvd_B₁_of_linear_of_nonneg_eval
    [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {π : Polynomial R} {a : R}
    (_hπ : Irreducible π) (_hπB₁ : π ∣ s.B₁)
    (hlin : Associated π (Polynomial.X - Polynomial.C a))
    (hnonneg : 0 ≤ (-C).eval a) :
    IsSquareMod π (-C) :=
  isSquareMod_linear_associated_of_nonneg_eval hlin hnonneg

theorem isSquareMod_neg_G_mul_C₁_iff_neg_C
    {π : Polynomial R} :
    IsSquareMod π (-(s.G * s.C₁)) ↔ IsSquareMod π (-C) := by
  have h : -(s.G * s.C₁) = -C := by
    rw [← s.hC]
  rw [h]

theorem isSquareMod_neg_G_mul_C₁_of_neg_C
    {π : Polynomial R} (h : IsSquareMod π (-C)) :
    IsSquareMod π (-(s.G * s.C₁)) :=
  (s.isSquareMod_neg_G_mul_C₁_iff_neg_C).mpr h

theorem isSquareMod_neg_G_mul_B₁_iff_neg_B
    {π : Polynomial R} :
    IsSquareMod π (-(s.G * s.B₁)) ↔ IsSquareMod π (-B) := by
  have h : -(s.G * s.B₁) = -B := by
    rw [← s.hB]
  rw [h]

theorem isSquareMod_neg_G_mul_B₁_of_neg_B
    {π : Polynomial R} (h : IsSquareMod π (-B)) :
    IsSquareMod π (-(s.G * s.B₁)) :=
  (s.isSquareMod_neg_G_mul_B₁_iff_neg_B).mpr h

end SquarefreeGcdSplit

/-!
The square-class normalization used below is obtained directly from the parity of the
factorization exponents.  In particular, `radical` alone is not a squarefree-part
decomposition: `P = radical P * divRadical P`, while the exponents of `divRadical P`
are one less than those of `P`.  The parity construction below keeps the odd exponents
in the squarefree factor and the even halves in the square factor.
-/

private theorem factorization_prod_pow_of_prime_support
    {R : Type*} [Field R] [Nontrivial R] [DecidableEq R]
    {f : Polynomial R →₀ ℕ}
    (hf : ∀ p ∈ f.support, Prime p)
    (hnorm : ∀ p ∈ f.support, normalize p = p) :
    factorization (f.prod (fun p n => p ^ n)) = f := by
  classical
  have haux : ∀ (s : Finset (Polynomial R)), s ⊆ f.support →
      factorization (∏ p ∈ s, p ^ f p) = ∑ p ∈ s, Finsupp.single p (f p) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simp
    | @insert a s ha ih =>
        intro hs
        have hfa : f a ≠ 0 :=
          Finsupp.mem_support_iff.mp (hs (Finset.mem_insert_self a s))
        have hpa : Prime a := hf a (hs (Finset.mem_insert_self a s))
        have hprod : (∏ p ∈ s, p ^ f p) ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          intro p hp
          exact pow_ne_zero _ ((hf p (hs (Finset.mem_insert_of_mem hp))).ne_zero)
        have hfa_fac : factorization a = Finsupp.single a 1 := by
          ext p
          rw [factorization_eq_count, normalizedFactors_irreducible hpa.irreducible]
          have hnorma := hnorm a (hs (Finset.mem_insert_self a s))
          rw [hnorma]
          by_cases h : p = a
          · subst p
            simp
          · have h' : a ≠ p := fun e => h e.symm
            simp only [Multiset.count_singleton, Finsupp.single_apply, ite_eq_right h, ite_eq_right h']
        rw [Finset.prod_insert ha, factorization_mul (pow_ne_zero _ hpa.ne_zero) hprod,
          factorization_pow, hfa_fac, ih (fun p hp => hs (Finset.mem_insert_of_mem hp))]
        rw [Finset.sum_insert ha]
        simp only [Finsupp.smul_single, nsmul_eq_mul, mul_one]
        rfl
  calc
    factorization (f.prod (fun p n => p ^ n)) =
        ∑ p ∈ f.support, Finsupp.single p (f p) := by
          simpa [Finsupp.prod] using haux f.support (by rfl)
    _ = f := by
      simpa [Finsupp.sum] using (Finsupp.sum_single f)

theorem exists_unit_mul_square_mul_squarefree_of_ne_zero
    {R : Type*} [Field R] [Nontrivial R] {P : Polynomial R} (hP : P ≠ 0) :
    ∃ (u : (Polynomial R)ˣ) (sf q : Polynomial R),
      Squarefree sf ∧ P = (u : Polynomial R) * sf * q ^ 2 := by
  classical
  let f : Polynomial R →₀ ℕ := factorization P
  let odd : Polynomial R →₀ ℕ :=
    Finsupp.mapRange (fun n => n % 2) (by simp) f
  let half : Polynomial R →₀ ℕ :=
    Finsupp.mapRange (fun n => n / 2) (by simp) f
  let sf : Polynomial R := odd.prod (fun p n => p ^ n)
  let q : Polynomial R := half.prod (fun p n => p ^ n)
  have hf_support : f.support =
      (UniqueFactorizationMonoid.normalizedFactors P).toFinset := by
    simp [f]
  have hodd_support : odd.support ⊆ f.support := Finsupp.support_mapRange
  have hhalf_support : half.support ⊆ f.support := Finsupp.support_mapRange
  have hodd_prime : ∀ p ∈ odd.support, Prime p := by
    intro p hp
    apply UniqueFactorizationMonoid.prime_of_normalized_factor p
    rw [← Multiset.mem_toFinset, ← hf_support]
    exact hodd_support hp
  have hhalf_prime : ∀ p ∈ half.support, Prime p := by
    intro p hp
    apply UniqueFactorizationMonoid.prime_of_normalized_factor p
    rw [← Multiset.mem_toFinset, ← hf_support]
    exact hhalf_support hp
  have hodd_norm : ∀ p ∈ odd.support, normalize p = p := by
    intro p hp
    apply normalize_normalized_factor p
    rw [← Multiset.mem_toFinset, ← hf_support]
    exact hodd_support hp
  have hhalf_norm : ∀ p ∈ half.support, normalize p = p := by
    intro p hp
    apply normalize_normalized_factor p
    rw [← Multiset.mem_toFinset, ← hf_support]
    exact hhalf_support hp
  have hsf_fac : factorization sf = odd := by
    simpa [sf] using factorization_prod_pow_of_prime_support hodd_prime hodd_norm
  have hq_fac : factorization q = half := by
    simpa [q] using factorization_prod_pow_of_prime_support hhalf_prime hhalf_norm
  have hsf0 : sf ≠ 0 := by
    rw [Finsupp.prod_ne_zero_iff]
    intro p hp
    exact pow_ne_zero _ ((hodd_prime p hp).ne_zero)
  have hq0 : q ≠ 0 := by
    rw [Finsupp.prod_ne_zero_iff]
    intro p hp
    exact pow_ne_zero _ ((hhalf_prime p hp).ne_zero)
  have hparity : odd + 2 • half = f := by
    ext p
    simp [odd, half]
    omega
  have hnodup : (UniqueFactorizationMonoid.normalizedFactors sf).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro p
    rw [← factorization_eq_count, hsf_fac]
    have hlt : odd p < 2 := by
      have hlt' : f p % 2 < 2 := Nat.mod_lt _ (by norm_num)
      simpa [odd] using hlt'
    omega
  have hsf_sq : Squarefree sf :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hsf0).mpr hnodup
  have hprod_fac : factorization (sf * q ^ 2) = f := by
    rw [factorization_mul hsf0 (pow_ne_zero 2 hq0), factorization_pow, hsf_fac, hq_fac,
      hparity]
  have hassoc : Associated (sf * q ^ 2) P := by
    apply associated_of_factorization_eq (sf * q ^ 2) P
    · exact mul_ne_zero hsf0 (pow_ne_zero 2 hq0)
    · exact hP
    · simpa [f] using hprod_fac
  rcases hassoc with ⟨u, hu⟩
  refine ⟨u, sf, q, hsf_sq, ?_⟩
  rw [← hu]
  simp [mul_assoc, mul_comm]

theorem exists_squarefree_mul_square_of_ne_zero
    {R : Type*} [Field R] [Nontrivial R] {P : Polynomial R} (hP : P ≠ 0) :
    ∃ (sf q : Polynomial R),
      sf ≠ 0 ∧ q ≠ 0 ∧ Squarefree sf ∧ P = sf * q ^ 2 := by
  rcases exists_unit_mul_square_mul_squarefree_of_ne_zero hP with
    ⟨u, sf, q, hsf, hdecomp⟩
  let sf' : Polynomial R := (u : Polynomial R) * sf
  have hsf' : Squarefree sf' := by
    apply (associated_unit_mul_left sf (u : Polynomial R) u.isUnit).squarefree_iff.mpr
    exact hsf
  have hsf'0 : sf' ≠ 0 := by
    exact mul_ne_zero (Units.ne_zero u) hsf.ne_zero
  have hq0 : q ≠ 0 := by
    intro hq
    subst q
    apply hP
    simpa using hdecomp
  refine ⟨sf', q, hsf'0, hq0, hsf', ?_⟩
  simpa [sf', mul_assoc] using hdecomp

theorem exists_squarefreeGcdSplit
    {R : Type u} [Field R] {B C : Polynomial R}
    (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hBsq : Squarefree B) (hCsq : Squarefree C) :
    Nonempty (SquarefreeGcdSplit B C) := by
  classical
  let G : Polynomial R := EuclideanDomain.gcd B C
  let B₁ : Polynomial R := B / G
  let C₁ : Polynomial R := C / G
  have hGdvdB : G ∣ B := by
    simpa [G] using EuclideanDomain.gcd_dvd_left B C
  have hGdvdC : G ∣ C := by
    simpa [G] using EuclideanDomain.gcd_dvd_right B C
  have hG0 : G ≠ 0 := ne_zero_of_dvd_ne_zero hB0 hGdvdB
  have hB : B = G * B₁ := by
    simpa [B₁, mul_comm] using (EuclideanDomain.mul_div_cancel' hG0 hGdvdB).symm
  have hC : C = G * C₁ := by
    simpa [C₁, mul_comm] using (EuclideanDomain.mul_div_cancel' hG0 hGdvdC).symm
  have hB₁0 : B₁ ≠ 0 := by
    intro hzero
    apply hB0
    rw [hB, hzero]
    simp
  have hC₁0 : C₁ ≠ 0 := by
    intro hzero
    apply hC0
    rw [hC, hzero]
    simp
  have hGsq : Squarefree G := hBsq.squarefree_of_dvd hGdvdB
  have hBmulSq : Squarefree (G * B₁) := by
    rwa [← hB]
  have hCmulSq : Squarefree (G * C₁) := by
    rwa [← hC]
  have hB₁sq : Squarefree B₁ := hBmulSq.of_mul_right
  have hC₁sq : Squarefree C₁ := hCmulSq.of_mul_right
  have hGB₁ : IsRelPrime G B₁ := IsRelPrime.of_squarefree_mul hBmulSq
  have hGC₁ : IsRelPrime G C₁ := IsRelPrime.of_squarefree_mul hCmulSq
  have hB₁C₁ : IsRelPrime B₁ C₁ := by
    intro D hDB₁ hDC₁
    have hDB : D ∣ B := by
      rw [hB]
      exact dvd_mul_of_dvd_right hDB₁ G
    have hDC : D ∣ C := by
      rw [hC]
      exact dvd_mul_of_dvd_right hDC₁ G
    have hDG : D ∣ G := by
      simpa [G] using EuclideanDomain.dvd_gcd hDB hDC
    exact hGB₁ hDG hDB₁
  exact ⟨
    { G := G
      B₁ := B₁
      C₁ := C₁
      G_ne_zero := hG0
      B₁_ne_zero := hB₁0
      C₁_ne_zero := hC₁0
      hB := hB
      hC := hC
      squarefree_G := hGsq
      squarefree_B₁ := hB₁sq
      squarefree_C₁ := hC₁sq
      relPrime_G_B₁ := hGB₁
      relPrime_G_C₁ := hGC₁
      relPrime_B₁_C₁ := hB₁C₁ }⟩

end RatFuncWittLocalGlobal
