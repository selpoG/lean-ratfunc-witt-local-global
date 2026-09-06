/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Polynomial.NormalForms
import RatFuncWittLocalGlobal.Polynomial.Mod
import RatFuncWittLocalGlobal.Polynomial.Roots
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Positivity and two-square facts for univariate polynomials

This module contains the nonnegative-polynomial and two-square auxiliary
theory used by the local-global reductions.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

def NonnegativePolynomialStandardFactorization
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (P : Polynomial R) : Prop :=
  ∃ (c : R), 0 ≤ c ∧
    ∃ (ι : Type u) (s : Finset ι) (r : ι → R) (n : ι → ℕ),
      (∀ i ∈ s, Even (n i)) ∧
        ∃ (κ : Type u) (t : Finset κ) (a b : κ → R),
          (∀ j ∈ t, 0 ≤ b j - (a j / 2) ^ 2) ∧
            P =
              Polynomial.C c *
                ((∏ i ∈ s, (Polynomial.X - Polynomial.C (r i)) ^ n i) *
                  (∏ j ∈ t,
                    (Polynomial.X ^ 2 + Polynomial.C (a j) * Polynomial.X + Polynomial.C (b j))))

theorem nonnegativePolynomialStandardFactorization_monic_quadratic
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (a : R) {b : R} (hb : 0 ≤ b - (a / 2) ^ 2) :
    NonnegativePolynomialStandardFactorization
      (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b) := by
  refine ⟨1, zero_le_one, PUnit, ∅, (fun _ => 0), (fun _ => 0), ?_,
    PUnit, {PUnit.unit}, (fun _ => a), (fun _ => b), ?_, ?_⟩
  · intro i hi
    simp at hi
  · intro j hj
    exact hb
  · simp

theorem NonnegativePolynomialStandardFactorization.of_eq
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {P Q : Polynomial R}
    (hP : NonnegativePolynomialStandardFactorization P) (h : Q = P) :
    NonnegativePolynomialStandardFactorization Q := by
  simpa [h] using hP

def PolynomialEverywhereNonnegative
    {R : Type u} [Semiring R] [LE R] (P : Polynomial R) : Prop :=
  ∀ x : R, 0 ≤ P.eval x

theorem polynomialEverywhereNonnegative_one
    {R : Type u} [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] :
    PolynomialEverywhereNonnegative (1 : Polynomial R) := by
  intro x
  simp

theorem polynomialEverywhereNonnegative_C
    {R : Type u} [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    {a : R} (ha : 0 ≤ a) :
    PolynomialEverywhereNonnegative (Polynomial.C a) := by
  intro x
  simpa using ha

theorem PolynomialEverywhereNonnegative.mul
    {R : Type u} [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    {P Q : Polynomial R}
    (hP : PolynomialEverywhereNonnegative P) (hQ : PolynomialEverywhereNonnegative Q) :
    PolynomialEverywhereNonnegative (P * Q) := by
  intro x
  rw [Polynomial.eval_mul]
  exact mul_nonneg (hP x) (hQ x)

theorem PolynomialEverywhereNonnegative.add
    {R : Type u} [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    {P Q : Polynomial R}
    (hP : PolynomialEverywhereNonnegative P) (hQ : PolynomialEverywhereNonnegative Q) :
    PolynomialEverywhereNonnegative (P + Q) := by
  intro x
  rw [Polynomial.eval_add]
  exact add_nonneg (hP x) (hQ x)

theorem polynomialEverywhereNonnegative_square
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (P : Polynomial R) :
    PolynomialEverywhereNonnegative (P ^ 2) := by
  intro x
  rw [Polynomial.eval_pow]
  simpa [sq] using sq_nonneg (P.eval x)

theorem polynomialEverywhereNonnegative_even_pow
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (P : Polynomial R) {n : ℕ} (hn : Even n) :
    PolynomialEverywhereNonnegative (P ^ n) := by
  rcases hn with ⟨m, rfl⟩
  simpa [pow_add, pow_two] using polynomialEverywhereNonnegative_square (P ^ m)

theorem polynomialEverywhereNonnegative_finset_prod
    {R : Type u} [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    {ι : Type*} (s : Finset ι) (P : ι → Polynomial R)
    (hP : ∀ i ∈ s, PolynomialEverywhereNonnegative (P i)) :
    PolynomialEverywhereNonnegative (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using (polynomialEverywhereNonnegative_one :
        PolynomialEverywhereNonnegative (1 : Polynomial R))
  | insert a s ha ih =>
      have haP : PolynomialEverywhereNonnegative (P a) :=
        hP a (Finset.mem_insert_self a s)
      have hsP : PolynomialEverywhereNonnegative (∏ i ∈ s, P i) :=
        ih fun i hi => hP i (Finset.mem_insert_of_mem hi)
      simpa [Finset.prod_insert, ha] using haP.mul hsP

theorem polynomialEverywhereNonnegative_X_add_C_sq_add_C_of_nonneg
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a : R) {b : R} (hb : 0 ≤ b) :
    PolynomialEverywhereNonnegative ((Polynomial.X + Polynomial.C a) ^ 2 + Polynomial.C b) :=
  (polynomialEverywhereNonnegative_square (Polynomial.X + Polynomial.C a)).add
    (polynomialEverywhereNonnegative_C hb)

theorem polynomialEverywhereNonnegative_monic_quadratic_of_two_mul_coeff
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (r : R) {b : R} (hb : 0 ≤ b - r ^ 2) :
    PolynomialEverywhereNonnegative
      (Polynomial.X ^ 2 + Polynomial.C (2 * r) * Polynomial.X + Polynomial.C b) := by
  have hsq :=
    polynomialEverywhereNonnegative_X_add_C_sq_add_C_of_nonneg r hb
  have hpoly :
      (Polynomial.X + Polynomial.C r) ^ 2 + Polynomial.C (b - r ^ 2) =
        Polynomial.X ^ 2 + Polynomial.C (2 * r) * Polynomial.X + Polynomial.C b := by
    simp [sq]
    ring_nf
    change
      Polynomial.X * Polynomial.C r * Polynomial.C (2 : R) + Polynomial.X ^ 2 +
          Polynomial.C b =
        Polynomial.X * Polynomial.C r * Polynomial.C (2 : R) + Polynomial.X ^ 2 +
          Polynomial.C b
    rfl
  rwa [hpoly] at hsq

theorem polynomialEverywhereNonnegative_monic_quadratic_of_completed_square_nonneg
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a : R) {b : R} (hb : 0 ≤ b - (a / 2) ^ 2) :
    PolynomialEverywhereNonnegative
      (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b) := by
  have hcoeff : (2 * (a / 2) : R) = a := by
    field_simp
  simpa [hcoeff] using
    (polynomialEverywhereNonnegative_monic_quadratic_of_two_mul_coeff
      (R := R) (a / 2) hb)

theorem monic_quadratic_completed_square_nonneg_of_irreducible
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a b : R}
    (hirr : Irreducible
      (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial R)) :
    0 ≤ b - (a / 2) ^ 2 := by
  by_contra hnot
  have hlt : b - (a / 2) ^ 2 < 0 := lt_of_not_ge hnot
  have hpos : 0 ≤ (a / 2) ^ 2 - b := by
    linarith
  rcases (IsSquare.of_nonneg hpos) with ⟨s, hs⟩
  have hroot :
      (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b :
        Polynomial R).IsRoot (-(a / 2) + s) := by
    rw [Polynomial.IsRoot]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C]
    exact calc
      (-(a / 2) + s) ^ 2 + a * (-(a / 2) + s) + b =
          s * s - ((a / 2) ^ 2 - b) := by ring
      _ = 0 := by
        rw [hs]
        ring
  have hdeg_one :
      (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b :
        Polynomial R).degree = 1 :=
    Polynomial.degree_eq_one_of_irreducible_of_root hirr hroot
  have hnat_one :
      (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b :
        Polynomial R).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some hdeg_one
  have hnat_two :
      (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b :
        Polynomial R).natDegree = 2 := by
    simpa using
      (Polynomial.natDegree_quadratic (a := (1 : R)) (b := a) (c := b)
        one_ne_zero)
  omega

theorem monic_quadratic_completed_square_pos_of_irreducible
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a b : R}
    (hirr : Irreducible
      (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial R)) :
    0 < b - (a / 2) ^ 2 := by
  have hnonneg := monic_quadratic_completed_square_nonneg_of_irreducible hirr
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  have hroot :
      (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b :
        Polynomial R).IsRoot (-(a / 2)) := by
    rw [Polynomial.IsRoot]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C]
    calc
      (-(a / 2)) ^ 2 + a * (-(a / 2)) + b = b - (a / 2) ^ 2 := by ring
      _ = 0 := hzero.symm
  have hdeg_one :
      (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b :
        Polynomial R).degree = 1 :=
    Polynomial.degree_eq_one_of_irreducible_of_root hirr hroot
  have hnat_one :
      (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b :
        Polynomial R).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some hdeg_one
  have hnat_two :
      (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b :
        Polynomial R).natDegree = 2 := by
    simpa using
      (Polynomial.natDegree_quadratic (a := (1 : R)) (b := a) (c := b)
        one_ne_zero)
  omega

theorem exists_imaginary_quadratic_square_coeffs_of_imag_zero
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {c : R} (hc : 0 < c) (x : R) :
    ∃ u v : R, u ^ 2 - c * v ^ 2 = x ∧ 2 * u * v = 0 := by
  by_cases hx : 0 ≤ x
  · rcases (IsSquare.of_nonneg hx) with ⟨u, hu⟩
    refine ⟨u, 0, ?_, ?_⟩
    · nlinarith [hu]
    · simp
  · have hxlt : x < 0 := lt_of_not_ge hx
    have hnonneg : 0 ≤ -x / c :=
      div_nonneg (neg_nonneg.mpr hxlt.le) hc.le
    rcases (IsSquare.of_nonneg hnonneg) with ⟨v, hv⟩
    refine ⟨0, v, ?_, ?_⟩
    · have hcne : c ≠ 0 := ne_of_gt hc
      field_simp [hcne] at hv
      nlinarith [hv]
    · simp

theorem exists_imaginary_quadratic_norm_sqrt_with_pos_half
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {c : R} (hc : 0 < c) {y : R} (hy : y ≠ 0) (x : R) :
    ∃ r : R, r ^ 2 = x ^ 2 + c * y ^ 2 ∧ 0 < (r + x) / 2 := by
  have hy_sq_pos : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hcy_sq_pos : 0 < c * y ^ 2 := mul_pos hc hy_sq_pos
  have hA_nonneg : 0 ≤ x ^ 2 + c * y ^ 2 := by
    nlinarith [sq_nonneg x, hcy_sq_pos.le]
  rcases (IsSquare.of_nonneg hA_nonneg) with ⟨s, hs⟩
  refine ⟨|s|, ?_, ?_⟩
  · simpa [sq_abs, sq] using hs.symm
  · have hr_nonneg : 0 ≤ |s| := abs_nonneg s
    have hr : x ^ 2 + c * y ^ 2 = |s| ^ 2 := by
      simpa [sq_abs, sq] using hs
    have hx_sq_lt : x ^ 2 < |s| ^ 2 := by
      nlinarith [hr, hcy_sq_pos]
    have hneg_abs_lt_x : -|s| < x :=
      (abs_lt_of_sq_lt_sq' hx_sq_lt hr_nonneg).1
    nlinarith

theorem exists_sqrt_of_pos_with_ne_zero
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {x : R} (hx : 0 < x) :
    ∃ u : R, u ^ 2 = x ∧ u ≠ 0 := by
  rcases (IsSquare.of_nonneg hx.le) with ⟨u, hu⟩
  refine ⟨u, ?_, ?_⟩
  · nlinarith [hu]
  · intro hu0
    nlinarith [hu]

theorem imaginary_quadratic_square_coeffs_of_norm_sqrt
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {c x y r u : R}
    (hr : r ^ 2 = x ^ 2 + c * y ^ 2)
    (hu : u ^ 2 = (r + x) / 2)
    (hu0 : u ≠ 0) :
    let v : R := y / (2 * u)
    u ^ 2 - c * v ^ 2 = x ∧ 2 * u * v = y := by
  let v : R := y / (2 * u)
  have hden : 2 * u ≠ 0 := mul_ne_zero two_ne_zero hu0
  have hden_sq : (2 * u) ^ 2 ≠ 0 := pow_ne_zero 2 hden
  have hv_mul : v * (2 * u) = y := by
    calc
      v * (2 * u) = (y / (2 * u)) * (2 * u) := by rfl
      _ = y := div_mul_cancel₀ y hden
  have hv_sq_mul : v ^ 2 * (2 * u) ^ 2 = y ^ 2 := by
    calc
      v ^ 2 * (2 * u) ^ 2 = (v * (2 * u)) ^ 2 := by ring
      _ = y ^ 2 := by rw [hv_mul]
  refine ⟨?_, ?_⟩
  · have hmain : 4 * u ^ 4 - c * y ^ 2 = 4 * u ^ 2 * x := by
      have h4u : 4 * u ^ 4 = (r + x) ^ 2 := by
        calc
          4 * u ^ 4 = 4 * (u ^ 2) ^ 2 := by ring
          _ = (r + x) ^ 2 := by
            rw [hu]
            ring
      have h4ux : 4 * u ^ 2 * x = 2 * x * (r + x) := by
        rw [hu]
        ring
      calc
        4 * u ^ 4 - c * y ^ 2 = (r + x) ^ 2 - c * y ^ 2 := by rw [h4u]
        _ = 2 * x * (r + x) := by nlinarith [hr]
        _ = 4 * u ^ 2 * x := by rw [h4ux]
    have hmul :
        (u ^ 2 - c * v ^ 2) * (2 * u) ^ 2 = x * (2 * u) ^ 2 := by
      rw [sub_mul, mul_assoc c, hv_sq_mul]
      ring_nf
      nlinarith [hmain]
    have hresult : u ^ 2 - c * v ^ 2 = x :=
      (mul_left_inj' hden_sq).mp
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    simpa [v, mul_comm, mul_left_comm, mul_assoc] using hresult
  · calc
      2 * u * v = v * (2 * u) := by ring
      _ = y := hv_mul

theorem exists_imaginary_quadratic_square_coeffs_of_imag_ne_zero
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {c : R} (hc : 0 < c) {y : R} (hy : y ≠ 0) (x : R) :
    ∃ u v : R, u ^ 2 - c * v ^ 2 = x ∧ 2 * u * v = y := by
  rcases exists_imaginary_quadratic_norm_sqrt_with_pos_half hc hy x with
    ⟨r, hr, hhalf⟩
  rcases exists_sqrt_of_pos_with_ne_zero hhalf with ⟨u, hu, hu0⟩
  refine ⟨u, y / (2 * u), ?_⟩
  simpa using imaginary_quadratic_square_coeffs_of_norm_sqrt
    (c := c) (x := x) (y := y) (r := r) (u := u) hr hu hu0

theorem exists_imaginary_quadratic_square_coeffs
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {c : R} (hc : 0 < c) (x y : R) :
    ∃ u v : R, u ^ 2 - c * v ^ 2 = x ∧ 2 * u * v = y := by
  by_cases hy : y = 0
  · rcases exists_imaginary_quadratic_square_coeffs_of_imag_zero hc x with
      ⟨u, v, hreal, himag⟩
    exact ⟨u, v, hreal, by simpa [hy] using himag⟩
  · exact exists_imaginary_quadratic_square_coeffs_of_imag_ne_zero hc hy x

theorem isSquareMod_X_sq_add_C_of_imaginary_quadratic_coeffs
    {R : Type u} [Field R] {c x y u v : R}
    (hreal : u ^ 2 - c * v ^ 2 = x) (himag : 2 * u * v = y) :
    IsSquareMod
      (Polynomial.X ^ 2 + Polynomial.C c)
      (Polynomial.C x + Polynomial.C y * Polynomial.X) := by
  refine ⟨Polynomial.C u + Polynomial.C v * Polynomial.X, ?_⟩
  rw [← Ideal.mem_span_singleton]
  refine Ideal.mem_span_singleton'.mpr ⟨Polynomial.C (v ^ 2), ?_⟩
  rw [← hreal, ← himag]
  simp only [Polynomial.C_mul, Polynomial.C_pow]
  have htwo_poly : (2 : Polynomial R) = Polynomial.C (2 : R) :=
    (Polynomial.C_eq_natCast (R := R) 2).symm
  ring_nf
  rw [htwo_poly]
  ring_nf
  rw [Polynomial.C_sub]
  simp only [Polynomial.C_mul, Polynomial.C_pow]
  ring_nf

theorem isSquareMod_X_sq_add_C_of_pos
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {c : R} (hc : 0 < c) (f : Polynomial R) :
    IsSquareMod (Polynomial.X ^ 2 + Polynomial.C c) f := by
  let q : Polynomial R := Polynomial.X ^ 2 + Polynomial.C c
  have hqmonic : q.Monic := by
    dsimp [q]
    simpa using
      (Polynomial.monic_X_pow_add_C (R := R) (a := c) (n := 2) (by norm_num))
  have hqne_one : q ≠ 1 := by
    dsimp [q]
    exact Polynomial.X_pow_add_C_ne_one (R := R) (n := 2) (by norm_num) c
  let r : Polynomial R := f %ₘ q
  have hrdeg : r.natDegree < 2 := by
    dsimp [r]
    simpa [q, Polynomial.natDegree_X_pow_add_C] using
      (Polynomial.natDegree_modByMonic_lt f hqmonic hqne_one)
  have hrlin :
      r = Polynomial.C (r.coeff 0) + Polynomial.C (r.coeff 1) * Polynomial.X :=
    Polynomial.eq_C_add_C_mul_X_of_natDegree_lt_two hrdeg
  rcases exists_imaginary_quadratic_square_coeffs hc (r.coeff 0) (r.coeff 1) with
    ⟨u, v, hreal, himag⟩
  have hsqr : IsSquareMod q r := by
    rw [hrlin]
    exact isSquareMod_X_sq_add_C_of_imaginary_quadratic_coeffs hreal himag
  rcases hsqr with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  have hfr : q ∣ f - r := by
    refine ⟨f /ₘ q, ?_⟩
    dsimp [r]
    rw [Polynomial.modByMonic_eq_sub_mul_div f q]
    ring
  have hrf : q ∣ r - f := by
    rcases hfr with ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    calc
      r - f = -(f - r) := by ring
      _ = -(q * a) := by rw [ha]
      _ = q * -a := by ring
  have hdecomp : w ^ 2 - f = (w ^ 2 - r) + (r - f) := by ring
  rw [hdecomp]
  exact dvd_add hw hrf

theorem IsSquareMod.comp
    {R : Type u} [Field R] {m a g : Polynomial R}
    (h : IsSquareMod m a) :
    IsSquareMod (m.comp g) (a.comp g) := by
  rcases h with ⟨w, hw⟩
  rcases hw with ⟨t, ht⟩
  refine ⟨w.comp g, ⟨t.comp g, ?_⟩⟩
  calc
    (w.comp g) ^ 2 - a.comp g = (w ^ 2 - a).comp g := by
      rw [Polynomial.sub_comp, Polynomial.pow_comp]
    _ = (m * t).comp g := by rw [ht]
    _ = m.comp g * t.comp g := by rw [Polynomial.mul_comp]

theorem isSquareMod_monic_quadratic_of_completed_square_pos
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a b : R} (hc : 0 < b - (a / 2) ^ 2) (f : Polynomial R) :
    IsSquareMod
      (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b)
      f := by
  let s : R := a / 2
  let c : R := b - s ^ 2
  have hc' : 0 < c := by simpa [c, s] using hc
  have hstd :
      IsSquareMod (Polynomial.X ^ 2 + Polynomial.C c)
        (f.comp (Polynomial.X - Polynomial.C s)) :=
    isSquareMod_X_sq_add_C_of_pos hc' (f.comp (Polynomial.X - Polynomial.C s))
  have hcomp := IsSquareMod.comp (g := Polynomial.X + Polynomial.C s) hstd
  convert hcomp using 1
  · simp [s, c, Polynomial.add_comp, Polynomial.pow_comp]
    ring_nf
    have htwo : (2 : Polynomial R) = Polynomial.C (2 : R) :=
      (Polynomial.C_eq_natCast (R := R) 2).symm
    rw [htwo]
    rw [mul_assoc]
    rw [← Polynomial.C_mul]
    ring_nf
  · have hinner :
        (Polynomial.X - Polynomial.C s).comp (Polynomial.X + Polynomial.C s) =
          (Polynomial.X : Polynomial R) := by
      simp [Polynomial.sub_comp]
    rw [Polynomial.comp_assoc, hinner, Polynomial.comp_X]

theorem Polynomial.eq_monic_quadratic_of_natDegree_eq_two
    {R : Type u} [Field R] {P : Polynomial R}
    (hmonic : P.Monic) (hdeg : P.natDegree = 2) :
    P = Polynomial.X ^ 2 + Polynomial.C (P.coeff 1) * Polynomial.X + Polynomial.C (P.coeff 0) := by
  have hdegree : P.degree ≤ (2 : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]
    exact le_rfl
  have hquad := Polynomial.eq_quadratic_of_degree_le_two hdegree
  have hcoeff_two : P.coeff 2 = 1 := by
    simpa [hdeg] using hmonic.coeff_natDegree
  rw [hquad, hcoeff_two]
  simp

theorem isSquareMod_irreducible_monic_natDegree_two
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {π f : Polynomial R}
    (hπ : Irreducible π) (hmonic : π.Monic) (hdeg : π.natDegree = 2) :
    IsSquareMod π f := by
  have hπeq := Polynomial.eq_monic_quadratic_of_natDegree_eq_two hmonic hdeg
  rw [hπeq]
  refine isSquareMod_monic_quadratic_of_completed_square_pos ?_ f
  have hquad_irreducible :
      Irreducible
        (Polynomial.X ^ 2 + Polynomial.C (π.coeff 1) * Polynomial.X +
          Polynomial.C (π.coeff 0) : Polynomial R) := by
    simpa [← hπeq] using hπ
  exact monic_quadratic_completed_square_pos_of_irreducible hquad_irreducible

theorem nonnegativePolynomialStandardFactorization_irreducible_monic_natDegree_two
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {π : Polynomial R}
    (hirr : Irreducible π) (hmonic : π.Monic) (hdeg : π.natDegree = 2) :
    NonnegativePolynomialStandardFactorization π := by
  have hπeq := Polynomial.eq_monic_quadratic_of_natDegree_eq_two hmonic hdeg
  have hquad_irreducible :
      Irreducible
        (Polynomial.X ^ 2 + Polynomial.C (π.coeff 1) * Polynomial.X +
          Polynomial.C (π.coeff 0) : Polynomial R) := by
    simpa [← hπeq] using hirr
  have hstd :
      NonnegativePolynomialStandardFactorization
        (Polynomial.X ^ 2 + Polynomial.C (π.coeff 1) * Polynomial.X +
          Polynomial.C (π.coeff 0) : Polynomial R) :=
    nonnegativePolynomialStandardFactorization_monic_quadratic (π.coeff 1)
      (monic_quadratic_completed_square_nonneg_of_irreducible hquad_irreducible)
  exact hstd.of_eq hπeq

theorem polynomialEverywhereNonnegative_of_standardFactorization
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {P : Polynomial R} (hP : NonnegativePolynomialStandardFactorization P) :
    PolynomialEverywhereNonnegative P := by
  rcases hP with ⟨c, hc, ι, s, r, n, hn, κ, t, a, b, hquad, hP⟩
  rw [hP]
  apply PolynomialEverywhereNonnegative.mul
  · exact polynomialEverywhereNonnegative_C hc
  · apply PolynomialEverywhereNonnegative.mul
    · exact polynomialEverywhereNonnegative_finset_prod s
        (fun i => (Polynomial.X - Polynomial.C (r i)) ^ n i)
        (fun i hi =>
          polynomialEverywhereNonnegative_even_pow
            (Polynomial.X - Polynomial.C (r i)) (hn i hi))
    · exact polynomialEverywhereNonnegative_finset_prod t
        (fun j => Polynomial.X ^ 2 + Polynomial.C (a j) * Polynomial.X + Polynomial.C (b j))
        (fun j hj =>
          polynomialEverywhereNonnegative_monic_quadratic_of_completed_square_nonneg
            (a j) (hquad j hj))

end RatFunc
end RatFuncWittLocalGlobal
