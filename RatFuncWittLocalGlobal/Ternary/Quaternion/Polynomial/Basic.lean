/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Ternary.Quaternion.Criterion.RealSplit
import RatFuncWittLocalGlobal.Ternary.Legendre.Polynomial.Definitions
import RatFuncWittLocalGlobal.Ternary.Legendre.ClearedBinary.Endpoint
import RatFuncWittLocalGlobal.Polynomial.InfinitySign
import Mathlib.Algebra.Squarefree.Basic

/-!
# RatFunc Quaternion-Symbol Interface

This file contains the concrete real-split side of the quaternion-symbol route
over `RatFunc R`.  Residue conditions and the global split criterion are kept
separate from this file.
-/

namespace RatFuncWittLocalGlobal

universe u v

variable {R : Type u}

/-- Normalized quaternion-symbol coefficient `-N/A` attached to a coefficient `N`. -/
noncomputable def polynomialTernaryQuaternionCoeff [Field R]
    (A N : Polynomial R) : RatFunc R :=
  -(algebraMap (Polynomial R) (RatFunc R) N /
      algebraMap (Polynomial R) (RatFunc R) A)

/-- The first normalized quaternion coefficient is nonzero when `A` and `B` are. -/
theorem polynomialTernaryQuaternion_squareClass_cleared
    [Field R] {A B C : Polynomial R} (hA0 : A ≠ 0) :
    RatFuncQuaternionSquareClass
      (polynomialTernaryQuaternionCoeff A B)
      (polynomialTernaryQuaternionCoeff A C)
      (algebraMap (Polynomial R) (RatFunc R) (-(A * B)))
      (algebraMap (Polynomial R) (RatFunc R) (-(A * C))) := by
  let φ := algebraMap (Polynomial R) (RatFunc R)
  have hAφ : φ A ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hA0
  refine ⟨(φ A)⁻¹, (φ A)⁻¹, inv_ne_zero hAφ, inv_ne_zero hAφ, ?_, ?_⟩
  · simp [polynomialTernaryQuaternionCoeff, φ, map_mul, map_neg]
    field_simp [hAφ]
  · simp [polynomialTernaryQuaternionCoeff, φ, map_mul, map_neg]
    field_simp [hAφ]

/--
Real split for the normalized symbol transfers to the cleared polynomial
symbol.
-/
theorem polynomialTernaryQuaternionRealSplit_cleared_of_normalized
    [Field R] {A B C : Polynomial R} (hA0 : A ≠ 0) :
    RatFuncQuaternionRealSplit.{u, v}
        (polynomialTernaryQuaternionCoeff A B)
        (polynomialTernaryQuaternionCoeff A C) →
      RatFuncQuaternionRealSplit.{u, v}
        (algebraMap (Polynomial R) (RatFunc R) (-(A * B)))
        (algebraMap (Polynomial R) (RatFunc R) (-(A * C))) :=
  ratFuncQuaternionSquareClass_transfers_realSplit
    (polynomialTernaryQuaternion_squareClass_cleared (R := R) hA0)

/--
Split of the cleared polynomial symbol transfers back to the normalized symbol.
-/
theorem polynomialTernaryQuaternionSplit_of_cleared
    [Field R] {A B C : Polynomial R} (hA0 : A ≠ 0) :
    QuaternionSymbolSplit
        (algebraMap (Polynomial R) (RatFunc R) (-(A * B)))
        (algebraMap (Polynomial R) (RatFunc R) (-(A * C))) →
      QuaternionSymbolSplit
        (polynomialTernaryQuaternionCoeff A B)
        (polynomialTernaryQuaternionCoeff A C) :=
  ratFuncQuaternionSquareClass_transfers_split
    (polynomialTernaryQuaternion_squareClass_cleared (R := R) hA0)

namespace RatFunc

/-!
The following lemmas isolate the concrete one-step Faddeev calculation behind
the whole-modulus square congruence.  The congruence witness is reduced modulo
`A`; its quotient is the next polynomial datum, and the same identity is a
quadratic-algebra norm equation.  The final cancellation is deliberately
conditional on a norm presentation of that quotient: this is the exact
one-step consumer, not a claim that one congruence already proves the
normalized ternary symbol is split.
-/

theorem reducedSquareModWitness_of_degree_bound
    [Field R] {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hAdeg : 0 < A.natDegree)
    (hBCdeg : B.natDegree + C.natDegree < 2 * A.natDegree)
    (h : IsSquareMod A (-(B * C))) :
    ∃ x d : Polynomial R,
      x ∈ Polynomial.degreeLT R A.natDegree ∧
        x ^ 2 + B * C = A * d ∧
          (d = 0 ∨ d.natDegree < A.natDegree) := by
  rcases h with ⟨x, hx⟩
  let xr : Polynomial.degreeLT R A.natDegree :=
    modByNonzeroDegreeLTLinearMap A hA0 x
  have hxr : A ∣ (xr : Polynomial R) ^ 2 + B * C := by
    apply dvd_square_add_of_modByNonzeroDegreeLTLinearMap hA0
    simpa [sub_eq_add_neg] using hx
  rcases hxr with ⟨d, hd⟩
  refine ⟨(xr : Polynomial R), d, xr.2, hd, ?_⟩
  by_cases hd0 : d = 0
  · exact Or.inl hd0
  · right
    have hxrdeg : (xr : Polynomial R).natDegree < A.natDegree := by
      by_cases hxr0 : (xr : Polynomial R) = 0
      · simp [hxr0, hAdeg]
      · exact polynomial_natDegree_lt_of_mem_degreeLT xr.2 hxr0
    have hsq_lt : ((xr : Polynomial R) ^ 2).natDegree < 2 * A.natDegree := by
      rw [Polynomial.natDegree_pow]
      omega
    have hbc_lt : (B * C).natDegree < 2 * A.natDegree :=
      lt_of_le_of_lt Polynomial.natDegree_mul_le hBCdeg
    have hsum_lt : ((xr : Polynomial R) ^ 2 + B * C).natDegree <
        2 * A.natDegree := by
      exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
        (max_lt hsq_lt hbc_lt)
    have hmul_lt : (A * d).natDegree < 2 * A.natDegree := by
      rw [← hd]
      exact hsum_lt
    rw [Polynomial.natDegree_mul hA0 hd0] at hmul_lt
    omega

/-!
The reduced representative has no freedom left inside `degreeLT`.  Adding a
multiple of the modulus changes the quotient by the displayed quadratic
expression, but it cannot produce another reduced representative.  We keep
both facts explicit because a gcd-removal argument cannot silently choose a
different residue representative.
-/

theorem squareModWitness_add_mul_quotient
    [CommRing R] {A B C x d t : Polynomial R}
    (hxd : x ^ 2 + B * C = A * d) :
    (x + A * t) ^ 2 + B * C =
      A * (d + 2 * x * t + A * t ^ 2) := by
  calc
    (x + A * t) ^ 2 + B * C =
        (x ^ 2 + B * C) + A * (2 * x * t + A * t ^ 2) := by ring
    _ = A * d + A * (2 * x * t + A * t ^ 2) := by rw [hxd]
    _ = A * (d + 2 * x * t + A * t ^ 2) := by ring

theorem squareModWitness_common_factor_of_squarefree_factor
    [Field R] {A B C x d r : Polynomial R}
    (hrsq : Squarefree r)
    (hrB : r ∣ B) (hrd : r ∣ d)
    (hxd : x ^ 2 + B * C = A * d) :
    ∃ x₁ B₁ d₁ : Polynomial R,
      x = r * x₁ ∧ B = r * B₁ ∧ d = r * d₁ ∧
        r * x₁ ^ 2 + B₁ * C = A * d₁ := by
  have hr0 : r ≠ 0 := hrsq.ne_zero
  have hrAd : r ∣ A * d := dvd_mul_of_dvd_right hrd A
  have hrBC : r ∣ B * C := dvd_mul_of_dvd_left hrB C
  have hx2eq : x ^ 2 = A * d - B * C := by
    rw [← hxd]
    ring
  have hrx2 : r ∣ x ^ 2 := by
    rw [hx2eq]
    exact dvd_sub hrAd hrBC
  have hrx : r ∣ x :=
    (hrsq.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp hrx2
  rcases hrx with ⟨x₁, hx⟩
  rcases hrB with ⟨B₁, hB⟩
  rcases hrd with ⟨d₁, hd⟩
  refine ⟨x₁, B₁, d₁, hx, hB, hd, ?_⟩
  apply mul_left_cancel₀ hr0
  calc
    r * (r * x₁ ^ 2 + B₁ * C) =
        (r * x₁) ^ 2 + (r * B₁) * C := by ring
    _ = A * (r * d₁) := by simpa [hx, hB, hd] using hxd
    _ = r * (A * d₁) := by ring

/-!
An irreducible pivot can force the zero quotient.  This is a genuine terminal
case for the recursive consumer below, not an admissibility certificate: when
the residue square is the unit square, an irreducible modulus has no nontrivial
degreeLT square root.
-/

def PolynomialTernaryClearedQuaternionSplit [Field R]
    (A B C : Polynomial R) : Prop :=
  QuaternionSymbolSplit
    (algebraMap (Polynomial R) (RatFunc R) (-(A * B)))
    (algebraMap (Polynomial R) (RatFunc R) (-(A * C)))

def PolynomialTernaryClearedQuaternionRealSplit [Field R]
    (A B C : Polynomial R) : Prop :=
  RatFuncQuaternionRealSplit.{u, v}
    (algebraMap (Polynomial R) (RatFunc R) (-(A * B)))
    (algebraMap (Polynomial R) (RatFunc R) (-(A * C)))

/-!
The cleared symbol attached to `(A,B,C)` is literally the unit-first symbol
attached to `(1,A*B,A*C)`.  This is the orientation used for the ordering
resolver: its obstruction concerns the cleared pair, not the raw pair `(B,C)`.
-/

theorem polynomialTernaryClearedQuaternionSplit_unit_first_iff
    [Field R] {A B C : Polynomial R} :
    PolynomialTernaryClearedQuaternionSplit A B C ↔
      PolynomialTernaryClearedQuaternionSplit 1 (A * B) (A * C) := by
  simp [PolynomialTernaryClearedQuaternionSplit]

theorem polynomialTernaryClearedQuaternionRealSplit_unit_first_iff
    [Field R] {A B C : Polynomial R} :
    PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
      PolynomialTernaryClearedQuaternionRealSplit.{u, v} 1 (A * B) (A * C) := by
  simp [PolynomialTernaryClearedQuaternionRealSplit]

theorem polynomialTernaryClearedQuaternionSplit_square_factor_transport
    [Field R] {A B C A' B' C' a b c : Polynomial R}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hA : A = A' * a ^ 2) (hB : B = B' * b ^ 2) (hC : C = C' * c ^ 2) :
    PolynomialTernaryClearedQuaternionSplit A B C ↔
      PolynomialTernaryClearedQuaternionSplit A' B' C' := by
  let φ := algebraMap (Polynomial R) (RatFunc R)
  have hAB : φ (-(A * B)) = φ (-(A' * B')) * φ (a * b) ^ 2 := by
    rw [hA, hB]
    simp [φ, map_mul, map_neg, map_pow]
    ring
  have hAC : φ (-(A * C)) = φ (-(A' * C')) * φ (a * c) ^ 2 := by
    rw [hA, hC]
    simp [φ, map_mul, map_neg, map_pow]
    ring
  have hab0 : φ (a * b) ≠ 0 :=
    _root_.RatFunc.algebraMap_ne_zero (mul_ne_zero ha0 hb0)
  have hac0 : φ (a * c) ≠ 0 :=
    _root_.RatFunc.algebraMap_ne_zero (mul_ne_zero ha0 hc0)
  change QuaternionSymbolSplit (φ (-(A * B))) (φ (-(A * C))) ↔
    QuaternionSymbolSplit (φ (-(A' * B'))) (φ (-(A' * C')))
  rw [hAB, hAC]
  exact (quaternionSymbolSplit_mul_square_left
      (u := φ (-(A' * B'))) (v := φ (-(A' * C')) * φ (a * c) ^ 2)
      (s := φ (a * b)) hab0).trans
    (quaternionSymbolSplit_mul_square_right
      (u := φ (-(A' * B'))) (v := φ (-(A' * C'))) (s := φ (a * c)) hac0)

theorem polynomialTernaryClearedQuaternionRealSplit_square_factor_transport
    [Field R] {A B C A' B' C' a b c : Polynomial R}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hA : A = A' * a ^ 2) (hB : B = B' * b ^ 2) (hC : C = C' * c ^ 2) :
    PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
      PolynomialTernaryClearedQuaternionRealSplit.{u, v} A' B' C' := by
  let φ := algebraMap (Polynomial R) (RatFunc R)
  have hAB : φ (-(A * B)) = φ (-(A' * B')) * φ (a * b) ^ 2 := by
    rw [hA, hB]
    simp [φ, map_mul, map_neg, map_pow]
    ring
  have hAC : φ (-(A * C)) = φ (-(A' * C')) * φ (a * c) ^ 2 := by
    rw [hA, hC]
    simp [φ, map_mul, map_neg, map_pow]
    ring
  have hab0 : φ (a * b) ≠ 0 :=
    _root_.RatFunc.algebraMap_ne_zero (mul_ne_zero ha0 hb0)
  have hac0 : φ (a * c) ≠ 0 :=
    _root_.RatFunc.algebraMap_ne_zero (mul_ne_zero ha0 hc0)
  change RatFuncQuaternionRealSplit.{u, v} (φ (-(A * B))) (φ (-(A * C))) ↔
    RatFuncQuaternionRealSplit.{u, v} (φ (-(A' * B'))) (φ (-(A' * C')))
  rw [hAB, hAC]
  exact (ratFuncQuaternionRealSplit_mul_square_left
      (R := R) (p := φ (-(A' * B')))
      (q := φ (-(A' * C')) * φ (a * c) ^ 2) (s := φ (a * b)) hab0).trans
    (ratFuncQuaternionRealSplit_mul_square_right
      (R := R) (p := φ (-(A' * B'))) (q := φ (-(A' * C'))) (s := φ (a * c)) hac0)

/-
Normalize a pairwise-coprime whole-modulus state to squarefree coefficient
representatives.  The congruence direction is deliberately explicit: the
old whole-modulus witness descends along the representative divisor, and the
square factors coming from the other two coefficients are cancelled using
their coprimality with that representative.
-/
theorem polynomialTernaryClearedQuaternionSplit_cyclic_iff
    [Field R] {A B C : Polynomial R} (hA0 : A ≠ 0) (hB0 : B ≠ 0) :
    PolynomialTernaryClearedQuaternionSplit A B C ↔
      PolynomialTernaryClearedQuaternionSplit B C A := by
  let φ := algebraMap (Polynomial R) (RatFunc R)
  have hAφ : φ A ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hA0
  have hBφ : φ B ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hB0
  let n : RatFunc R := φ B / φ A
  have hn0 : n ≠ 0 := by
    exact div_ne_zero hBφ hAφ
  have hnorm : n = (0 : RatFunc R) ^ 2 - φ (-(A * B)) * (φ A)⁻¹ ^ 2 := by
    dsimp [n]
    simp [φ, map_mul, map_neg]
    field_simp [hAφ]
  have hprod : φ (-(B * C)) * n = φ (-(A * C)) * n ^ 2 := by
    dsimp [n]
    simp [φ, map_mul, map_neg]
    field_simp [hAφ]
  change
    QuaternionSymbolSplit (φ (-(A * B))) (φ (-(A * C))) ↔
      QuaternionSymbolSplit (φ (-(B * C))) (φ (-(B * A)))
  calc
    QuaternionSymbolSplit (φ (-(A * B))) (φ (-(A * C))) ↔
        QuaternionSymbolSplit (φ (-(A * C))) (φ (-(A * B))) :=
      quaternionSymbolSplit_comm
    _ ↔ QuaternionSymbolSplit (φ (-(A * C)) * n ^ 2) (φ (-(A * B))) := by
      exact (quaternionSymbolSplit_mul_square_left hn0).symm
    _ ↔ QuaternionSymbolSplit (φ (-(B * C)) * n) (φ (-(A * B))) := by
      rw [hprod]
    _ ↔ QuaternionSymbolSplit (φ (-(B * C))) (φ (-(A * B))) :=
      quaternionSymbolSplit_mul_norm_left_iff hnorm hn0
    _ ↔ QuaternionSymbolSplit (φ (-(B * C))) (φ (-(B * A))) := by
      simp [φ, map_mul, map_neg, mul_comm]

theorem polynomialTernaryClearedQuaternionSplit_descent
    [Field R] {A B C x d : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hd : x ^ 2 + B * C = A * d) :
    PolynomialTernaryClearedQuaternionSplit A B C ↔
      PolynomialTernaryClearedQuaternionSplit B C d := by
  let φ := algebraMap (Polynomial R) (RatFunc R)
  have hcyc :
      PolynomialTernaryClearedQuaternionSplit A B C ↔
        PolynomialTernaryClearedQuaternionSplit B C A :=
    polynomialTernaryClearedQuaternionSplit_cyclic_iff hA0 hB0
  change
    QuaternionSymbolSplit (φ (-(A * B))) (φ (-(A * C))) ↔
      QuaternionSymbolSplit (φ (-(B * C))) (φ (-(B * d)))
  have hnorm : φ (A * d) = φ x ^ 2 - φ (-(B * C)) * (1 : RatFunc R) ^ 2 := by
    simpa [φ, map_mul, map_add, map_neg, pow_two] using (congrArg φ hd).symm
  by_cases hd0 : d = 0
  · have hsquare : IsSquare (φ (-(B * C))) := by
      refine ⟨φ x, ?_⟩
      have hsq : -(B * C) = x ^ 2 := by
        rw [hd0] at hd
        linear_combination -hd
      simpa [φ, map_mul, map_add, map_neg, pow_two] using congrArg φ hsq
    have hcyclic :
        QuaternionSymbolSplit (φ (-(B * C))) (φ (-(A * B))) :=
      quaternionSymbolSplit_of_isSquare_left hsquare
    have hsource :
        QuaternionSymbolSplit (φ (-(A * B))) (φ (-(A * C))) :=
      hcyc.mpr (by
        simpa [PolynomialTernaryClearedQuaternionSplit, φ, map_mul, map_neg,
          mul_comm] using hcyclic)
    have htarget :
        QuaternionSymbolSplit (φ (-(B * C))) (φ (-(B * d))) := by
      rw [hd0]
      exact quaternionSymbolSplit_of_right_eq_zero (by simp)
    exact ⟨fun _ => htarget, fun _ => hsource⟩
  · have hAφ : φ A ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hA0
    have hn0 : φ (A * d) ≠ 0 :=
      _root_.RatFunc.algebraMap_ne_zero (mul_ne_zero hA0 hd0)
    have hprod :
        φ (-(B * d)) * φ A ^ 2 = φ (-(A * B)) * φ (A * d) := by
      simp [φ, map_mul, map_neg, pow_two]
      ring
    have hreciff :
        QuaternionSymbolSplit (φ (-(B * C))) (φ (-(B * d))) ↔
          QuaternionSymbolSplit (φ (-(B * C))) (φ (-(A * B))) := by
      calc
        QuaternionSymbolSplit (φ (-(B * C))) (φ (-(B * d))) ↔
            QuaternionSymbolSplit (φ (-(B * d)) * φ A ^ 2) (φ (-(B * C))) := by
          rw [quaternionSymbolSplit_comm]
          exact (quaternionSymbolSplit_mul_square_left
            (u := φ (-(B * d))) (v := φ (-(B * C))) hAφ).symm
        _ ↔ QuaternionSymbolSplit (φ (-(A * B)) * φ (A * d)) (φ (-(B * C))) := by
          rw [hprod]
        _ ↔ QuaternionSymbolSplit (φ (-(B * C)))
              (φ (-(A * B)) * φ (A * d)) := quaternionSymbolSplit_comm
        _ ↔ QuaternionSymbolSplit (φ (-(B * C))) (φ (-(A * B))) :=
          (quaternionSymbolSplit_mul_norm_right_iff
            (u := φ (-(B * C))) (v := φ (-(A * B)))
            (n := φ (A * d)) (α := φ x) (β := (1 : RatFunc R))
            hnorm hn0)
    constructor
    · intro hsource
      have hcyclic :
          PolynomialTernaryClearedQuaternionSplit B C A := hcyc.mp hsource
      apply hreciff.mpr
      simpa [PolynomialTernaryClearedQuaternionSplit, φ, map_mul, map_neg,
        mul_comm] using hcyclic
    · intro htarget
      have hcyclic :
          QuaternionSymbolSplit (φ (-(B * C))) (φ (-(A * B))) :=
        hreciff.mp htarget
      apply hcyc.mpr
      simpa [PolynomialTernaryClearedQuaternionSplit, φ, map_mul, map_neg,
        mul_comm] using hcyclic

/-!
The squarefree gcd extraction has a weighted recursive consumer.  If the
equation is `g * x^2 + B * C = A * d`, multiplying by `g` gives the ordinary
descent equation for the triple `(A, g * B, C)`.  The resulting square factor
`g^2` in the second recursive coefficient can be removed, but the factor `g`
must move to the other coefficient.  Thus the honest target is
`S(B, g * C, d)`, not `S(B, C, d)`.
-/

theorem polynomialTernaryClearedQuaternionSplit_weighted_descent
    [Field R] {A B C d g x : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hg0 : g ≠ 0)
    (hxd : g * x ^ 2 + B * C = A * d) :
    PolynomialTernaryClearedQuaternionSplit A (g * B) C ↔
      PolynomialTernaryClearedQuaternionSplit B (g * C) d := by
  have hmul : (g * x) ^ 2 + (g * B) * C = A * (g * d) := by
    calc
      (g * x) ^ 2 + (g * B) * C = g * (g * x ^ 2 + B * C) := by ring
      _ = g * (A * d) := by rw [hxd]
      _ = A * (g * d) := by ring
  have hdesc := polynomialTernaryClearedQuaternionSplit_descent
    (A := A) (B := g * B) (C := C) (x := g * x) (d := g * d)
    hA0 (mul_ne_zero hg0 hB0) hmul
  let φ := algebraMap (Polynomial R) (RatFunc R)
  have hgφ : φ g ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hg0
  have hfactor :
      PolynomialTernaryClearedQuaternionSplit (g * B) C (g * d) ↔
        PolynomialTernaryClearedQuaternionSplit B (g * C) d := by
    change QuaternionSymbolSplit (φ (-(g * B * C)))
        (φ (-(g * B * (g * d)))) ↔
      QuaternionSymbolSplit (φ (-(B * (g * C)))) (φ (-(B * d)))
    have hfirst : φ (-(g * B * C)) = φ (-(B * (g * C))) := by
      simp [φ, map_mul, map_neg]
      ring
    have hsecond : φ (-(g * B * (g * d))) =
        φ (-(B * d)) * φ g ^ 2 := by
      simp [φ, map_mul, map_neg, pow_two]
      ring
    rw [hfirst, hsecond]
    exact quaternionSymbolSplit_mul_square_right hgφ
  exact hdesc.trans hfactor

theorem polynomialLegendreWholeModConditions_common_factor_transport
    [Field R] {A B C g x₁ B₁ d₁ : Polynomial R}
    (hwhole : PolynomialLegendreWholeModConditions A B C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hBC : IsCoprime B C)
    (hgB : g ∣ B) (hBfac : B = g * B₁)
    (hweighted : g * x₁ ^ 2 + B₁ * C = A * d₁)
    (hB₁d₁ : IsCoprime B₁ d₁) :
    PolynomialLegendreWholeModConditions B₁ (g * C) d₁ := by
  have hB₁dvdB : B₁ ∣ B := by
    refine ⟨g, ?_⟩
    simpa [mul_comm] using hBfac
  have hGC : IsCoprime g C :=
    hBC.of_isCoprime_of_dvd_left hgB
  have hAB₁ : IsCoprime A B₁ :=
    hAB.of_isCoprime_of_dvd_right hB₁dvdB
  have hAd₁B₁ : IsCoprime (A * d₁) B₁ :=
    hAB₁.mul_left hB₁d₁.symm
  have hsum : IsCoprime (g * x₁ ^ 2 + B₁ * C) B₁ := by
    rw [hweighted]
    exact hAd₁B₁
  have hgxB₁ : IsCoprime (g * x₁ ^ 2) B₁ :=
    hsum.of_add_mul_left_left
  have hx₁sqB₁ : IsCoprime (x₁ ^ 2) B₁ :=
    hgxB₁.of_mul_left_right
  have hx₁B₁ : IsCoprime x₁ B₁ :=
    by simpa [one_mul] using hx₁sqB₁.of_mul_left_left
  rcases hwhole with ⟨_hA, hB, hC⟩
  have hB₁old : IsSquareMod B₁ (-(A * C)) :=
    hB.of_dvd hB₁dvdB
  have hrelB₁ : B₁ ∣ A * d₁ - g * x₁ ^ 2 := by
    refine ⟨C, ?_⟩
    calc
      A * d₁ - g * x₁ ^ 2 =
          (g * x₁ ^ 2 + B₁ * C) - g * x₁ ^ 2 := by rw [hweighted]
      _ = B₁ * C := by ring
  have hB₁cong : B₁ ∣
      (-(A * C) * d₁ ^ 2) - ((-(g * C * d₁)) * x₁ ^ 2) := by
    rw [show
      (-(A * C) * d₁ ^ 2) - ((-(g * C * d₁)) * x₁ ^ 2) =
        -(A * d₁ - g * x₁ ^ 2) * (C * d₁) by ring]
    simpa only [neg_mul] using
      (dvd_neg.mpr (dvd_mul_of_dvd_left hrelB₁ (C * d₁)))
  have hB₁q : IsSquareMod B₁ ((-(g * C * d₁)) * x₁ ^ 2) := by
    exact hB₁old.mul_square d₁ |>.of_dvd_sub hB₁cong
  have hB₁new : IsSquareMod B₁ (-(g * C * d₁)) :=
    IsSquareMod.of_mul_square_of_isCoprime hx₁B₁ hB₁q
  have hrelC : C ∣ A * d₁ - g * x₁ ^ 2 := by
    refine ⟨B₁, ?_⟩
    calc
      A * d₁ - g * x₁ ^ 2 =
          (g * x₁ ^ 2 + B₁ * C) - g * x₁ ^ 2 := by rw [hweighted]
      _ = C * B₁ := by ring
  have hCold : IsSquareMod C (-(A * (g * B₁))) := by
    simpa [hBfac] using hC
  have hCcong : C ∣
      (-(A * (g * B₁)) * x₁ ^ 2) - ((-(B₁ * d₁)) * A ^ 2) := by
    rw [show
      (-(A * (g * B₁)) * x₁ ^ 2) - ((-(B₁ * d₁)) * A ^ 2) =
        (B₁ * A) * (A * d₁ - g * x₁ ^ 2) by ring]
    exact dvd_mul_of_dvd_right hrelC (B₁ * A)
  have hCq : IsSquareMod C ((-(B₁ * d₁)) * A ^ 2) := by
    exact hCold.mul_square x₁ |>.of_dvd_sub hCcong
  have hCnew : IsSquareMod C (-(B₁ * d₁)) :=
    IsSquareMod.of_mul_square_of_isCoprime hAC hCq
  have hGold : IsSquareMod g (-(A * C)) :=
    hB.of_dvd hgB
  have hrelG : g ∣ A * d₁ - B₁ * C := by
    refine ⟨x₁ ^ 2, ?_⟩
    calc
      A * d₁ - B₁ * C =
          (g * x₁ ^ 2 + B₁ * C) - B₁ * C := by rw [hweighted]
      _ = g * x₁ ^ 2 := by ring
  have hGcong : g ∣
      (-(A * C) * d₁ ^ 2) - ((-(B₁ * d₁)) * C ^ 2) := by
    rw [show
      (-(A * C) * d₁ ^ 2) - ((-(B₁ * d₁)) * C ^ 2) =
        -(A * d₁ - B₁ * C) * (C * d₁) by ring]
    simpa only [neg_mul] using
      (dvd_neg.mpr (dvd_mul_of_dvd_left hrelG (C * d₁)))
  have hGq : IsSquareMod g ((-(B₁ * d₁)) * C ^ 2) := by
    exact hGold.mul_square d₁ |>.of_dvd_sub hGcong
  have hGnew : IsSquareMod g (-(B₁ * d₁)) :=
    IsSquareMod.of_mul_square_of_isCoprime hGC.symm hGq
  have hGCnew : IsSquareMod (g * C) (-(B₁ * d₁)) :=
    isSquareMod_mul_of_isCoprime hGC hGnew hCnew
  have hd₁new : IsSquareMod d₁ (-(B₁ * (g * C))) := by
    refine ⟨g * x₁, ?_⟩
    refine ⟨g * A, ?_⟩
    calc
      (g * x₁) ^ 2 - (-(B₁ * (g * C))) =
          g * (g * x₁ ^ 2 + B₁ * C) := by ring
      _ = g * (A * d₁) := by rw [hweighted]
      _ = d₁ * (g * A) := by ring
  exact ⟨hB₁new, hGCnew, hd₁new⟩

theorem polynomialTernaryClearedQuaternionRealSplit_cyclic_iff
    [Field R] {A B C : Polynomial R} (hA0 : A ≠ 0) (hB0 : B ≠ 0) :
    PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
      PolynomialTernaryClearedQuaternionRealSplit.{u, v} B C A := by
  let φ := algebraMap (Polynomial R) (RatFunc R)
  have hAφ : φ A ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hA0
  have hBφ : φ B ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hB0
  let n : RatFunc R := φ B / φ A
  have hn0 : n ≠ 0 := div_ne_zero hBφ hAφ
  have hnorm : n = (0 : RatFunc R) ^ 2 - φ (-(A * B)) * (φ A)⁻¹ ^ 2 := by
    dsimp [n]
    simp [φ, map_mul, map_neg]
    field_simp [hAφ]
  have hprod : φ (-(B * C)) * n = φ (-(A * C)) * n ^ 2 := by
    dsimp [n]
    simp [φ, map_mul, map_neg]
    field_simp [hAφ]
  change
    RatFuncQuaternionRealSplit.{u, v} (φ (-(A * B))) (φ (-(A * C))) ↔
      RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C))) (φ (-(B * A)))
  calc
    RatFuncQuaternionRealSplit.{u, v} (φ (-(A * B))) (φ (-(A * C))) ↔
        RatFuncQuaternionRealSplit.{u, v} (φ (-(A * C))) (φ (-(A * B))) :=
      ratFuncQuaternionRealSplit_comm
    _ ↔ RatFuncQuaternionRealSplit.{u, v} (φ (-(A * C)) * n ^ 2) (φ (-(A * B))) := by
      exact (ratFuncQuaternionRealSplit_mul_square_left hn0).symm
    _ ↔ RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C)) * n) (φ (-(A * B))) := by
      rw [hprod]
    _ ↔ RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C))) (φ (-(A * B))) :=
      ratFuncQuaternionRealSplit_mul_norm_left hnorm hn0
    _ ↔ RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C))) (φ (-(B * A))) := by
      simp only [mul_comm B A]

/-!
The common-factor cyclic move is the symbol-level operation needed when a
gcd is removed from two slots.  It is unconditional at the symbol level:
the factor contributes only a square to the first cleared coefficient.
-/

theorem polynomialTernaryClearedQuaternionSplit_common_factor_cyclic_transport
    [Field R] {A B C h : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hh0 : h ≠ 0) :
    PolynomialTernaryClearedQuaternionSplit A (h * B) (h * C) ↔
      PolynomialTernaryClearedQuaternionSplit B C (h * A) := by
  have hcyc := polynomialTernaryClearedQuaternionSplit_cyclic_iff
    (A := A) (B := h * B) (C := h * C) hA0 (mul_ne_zero hh0 hB0)
  have hφ : algebraMap (Polynomial R) (RatFunc R) h ≠ 0 :=
    _root_.RatFunc.algebraMap_ne_zero hh0
  have hfactor :
      PolynomialTernaryClearedQuaternionSplit (h * B) (h * C) A ↔
        PolynomialTernaryClearedQuaternionSplit B C (h * A) := by
    change QuaternionSymbolSplit
        (algebraMap (Polynomial R) (RatFunc R) (-(h * B * (h * C))))
        (algebraMap (Polynomial R) (RatFunc R) (-(h * B * A))) ↔
      QuaternionSymbolSplit
        (algebraMap (Polynomial R) (RatFunc R) (-(B * C)))
        (algebraMap (Polynomial R) (RatFunc R) (-(B * (h * A))))
    have hfirst :
        algebraMap (Polynomial R) (RatFunc R) (-(h * B * (h * C))) =
          algebraMap (Polynomial R) (RatFunc R) (-(B * C)) *
            algebraMap (Polynomial R) (RatFunc R) h ^ 2 := by
      simp [map_mul, map_neg, pow_two]
      ring
    have hsecond :
        algebraMap (Polynomial R) (RatFunc R) (-(h * B * A)) =
          algebraMap (Polynomial R) (RatFunc R) (-(B * (h * A))) := by
      simp [map_mul, map_neg]
      ring
    rw [hfirst, hsecond]
    exact quaternionSymbolSplit_mul_square_left hφ
  exact hcyc.trans hfactor

theorem polynomialTernaryClearedQuaternionRealSplit_common_factor_cyclic_transport
    [Field R] {A B C h : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hh0 : h ≠ 0) :
    PolynomialTernaryClearedQuaternionRealSplit.{u, v} A (h * B) (h * C) ↔
      PolynomialTernaryClearedQuaternionRealSplit.{u, v} B C (h * A) := by
  have hcyc := polynomialTernaryClearedQuaternionRealSplit_cyclic_iff
    (A := A) (B := h * B) (C := h * C) hA0 (mul_ne_zero hh0 hB0)
  have hφ : algebraMap (Polynomial R) (RatFunc R) h ≠ 0 :=
    _root_.RatFunc.algebraMap_ne_zero hh0
  have hfactor :
      PolynomialTernaryClearedQuaternionRealSplit.{u, v} (h * B) (h * C) A ↔
        PolynomialTernaryClearedQuaternionRealSplit.{u, v} B C (h * A) := by
    change RatFuncQuaternionRealSplit.{u, v}
        (algebraMap (Polynomial R) (RatFunc R) (-(h * B * (h * C))))
        (algebraMap (Polynomial R) (RatFunc R) (-(h * B * A))) ↔
      RatFuncQuaternionRealSplit.{u, v}
        (algebraMap (Polynomial R) (RatFunc R) (-(B * C)))
        (algebraMap (Polynomial R) (RatFunc R) (-(B * (h * A))))
    have hfirst :
        algebraMap (Polynomial R) (RatFunc R) (-(h * B * (h * C))) =
          algebraMap (Polynomial R) (RatFunc R) (-(B * C)) *
            algebraMap (Polynomial R) (RatFunc R) h ^ 2 := by
      simp [map_mul, map_neg, pow_two]
      ring
    have hsecond :
        algebraMap (Polynomial R) (RatFunc R) (-(h * B * A)) =
          algebraMap (Polynomial R) (RatFunc R) (-(B * (h * A))) := by
      simp [map_mul, map_neg]
      ring
    rw [hfirst, hsecond]
    exact ratFuncQuaternionRealSplit_mul_square_left hφ
  exact hcyc.trans hfactor

/-!
The corresponding whole-modulus transport has one genuine arithmetic
premise.  The old `A` congruence only gives a square modulo `A` after the
factor `h` is removed; the new modulus `h * A` also needs `h` itself to see
the target `-(B * C)` as a square.  The coprimality hypothesis is exactly
what permits cancellation and recombination of these two congruences.
-/

theorem polynomialTernaryClearedQuaternionRealSplit_descent
    [Field R] {A B C x d : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hd : x ^ 2 + B * C = A * d) :
    PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
      PolynomialTernaryClearedQuaternionRealSplit.{u, v} B C d := by
  let φ := algebraMap (Polynomial R) (RatFunc R)
  have hcyc :
      PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
        PolynomialTernaryClearedQuaternionRealSplit.{u, v} B C A :=
    polynomialTernaryClearedQuaternionRealSplit_cyclic_iff (R := R) hA0 hB0
  change
    RatFuncQuaternionRealSplit.{u, v} (φ (-(A * B))) (φ (-(A * C))) ↔
      RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C))) (φ (-(B * d)))
  have hnorm : φ (A * d) = φ x ^ 2 - φ (-(B * C)) * (1 : RatFunc R) ^ 2 := by
    simpa [φ, map_mul, map_add, map_neg, pow_two] using (congrArg φ hd).symm
  by_cases hd0 : d = 0
  · have hsquare : IsSquare (φ (-(B * C))) := by
      refine ⟨φ x, ?_⟩
      have hsq : -(B * C) = x ^ 2 := by
        rw [hd0] at hd
        linear_combination -hd
      simpa [φ, map_mul, map_add, map_neg, pow_two] using congrArg φ hsq
    have hcyclic :
        RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C))) (φ (-(A * B))) := by
      intro K hKField hKOrder hKStrict hKRealClosed hKAlg
      let _ : Field K := hKField
      let _ : LinearOrder K := hKOrder
      let _ : IsStrictOrderedRing K := hKStrict
      let _ : IsRealClosed K := hKRealClosed
      let _ : Algebra (RatFunc R) K := hKAlg
      exact quaternionSymbolSplit_baseChange (F := RatFunc R) (K := K)
        (quaternionSymbolSplit_of_isSquare_left hsquare)
    have hcyclic' :
        PolynomialTernaryClearedQuaternionRealSplit.{u, v} B C A := by
      change RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C))) (φ (-(B * A)))
      intro K hKField hKOrder hKStrict hKRealClosed hKAlg
      let _ : Field K := hKField
      let _ : LinearOrder K := hKOrder
      let _ : IsStrictOrderedRing K := hKStrict
      let _ : IsRealClosed K := hKRealClosed
      let _ : Algebra (RatFunc R) K := hKAlg
      simpa only [mul_comm B A] using hcyclic (K := K)
    have hsource' :
        PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C := by
      rw [hcyc]
      exact hcyclic'
    have hsource :
        RatFuncQuaternionRealSplit.{u, v} (φ (-(A * B))) (φ (-(A * C))) := by
      exact hsource'
    have htarget :
        RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C))) (φ (-(B * d))) := by
      rw [hd0]
      intro K hKField hKOrder hKStrict hKRealClosed hKAlg
      let _ : Field K := hKField
      let _ : LinearOrder K := hKOrder
      let _ : IsStrictOrderedRing K := hKStrict
      let _ : IsRealClosed K := hKRealClosed
      let _ : Algebra (RatFunc R) K := hKAlg
      exact quaternionSymbolSplit_baseChange (F := RatFunc R) (K := K)
        (quaternionSymbolSplit_of_right_eq_zero (by simp))
    exact ⟨fun _ => htarget, fun _ => hsource⟩
  · have hAφ : φ A ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hA0
    have hn0 : φ (A * d) ≠ 0 :=
      _root_.RatFunc.algebraMap_ne_zero (mul_ne_zero hA0 hd0)
    have hprod : φ (-(B * d)) * φ A ^ 2 = φ (-(A * B)) * φ (A * d) := by
      simp [φ, map_mul, map_neg, pow_two]
      ring
    have hreciff :
        RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C))) (φ (-(B * d))) ↔
          RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C))) (φ (-(A * B))) := by
      calc
        RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C))) (φ (-(B * d))) ↔
            RatFuncQuaternionRealSplit.{u, v} (φ (-(B * d)) * φ A ^ 2)
              (φ (-(B * C))) := by
          rw [ratFuncQuaternionRealSplit_comm]
          exact (ratFuncQuaternionRealSplit_mul_square_left
            (p := φ (-(B * d))) (q := φ (-(B * C))) (s := φ A) hAφ).symm
        _ ↔ RatFuncQuaternionRealSplit.{u, v} (φ (-(A * B)) * φ (A * d))
              (φ (-(B * C))) := by
          rw [hprod]
        _ ↔ RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C)))
              (φ (-(A * B)) * φ (A * d)) := ratFuncQuaternionRealSplit_comm
        _ ↔ RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C))) (φ (-(A * B))) :=
          ratFuncQuaternionRealSplit_mul_norm_right hnorm hn0
    constructor
    · intro hsource
      have hcyclic :
          PolynomialTernaryClearedQuaternionRealSplit.{u, v} B C A := hcyc.mp hsource
      apply hreciff.mpr
      intro K hKField hKOrder hKStrict hKRealClosed hKAlg
      let _ : Field K := hKField
      let _ : LinearOrder K := hKOrder
      let _ : IsStrictOrderedRing K := hKStrict
      let _ : IsRealClosed K := hKRealClosed
      let _ : Algebra (RatFunc R) K := hKAlg
      simpa only [mul_comm B A] using hcyclic (K := K)
    · intro htarget
      have hcyclic :
          RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C))) (φ (-(A * B))) :=
        hreciff.mp htarget
      have hcyclic' :
          PolynomialTernaryClearedQuaternionRealSplit.{u, v} B C A := by
        change RatFuncQuaternionRealSplit.{u, v} (φ (-(B * C))) (φ (-(B * A)))
        intro K hKField hKOrder hKStrict hKRealClosed hKAlg
        let _ : Field K := hKField
        let _ : LinearOrder K := hKOrder
        let _ : IsStrictOrderedRing K := hKStrict
        let _ : IsRealClosed K := hKRealClosed
        let _ : Algebra (RatFunc R) K := hKAlg
        simpa only [mul_comm B A] using hcyclic (K := K)
      change PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C
      rw [hcyc]
      exact hcyclic'

theorem polynomialTernaryClearedQuaternionRealSplit_weighted_descent
    [Field R] {A B C d g x : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hg0 : g ≠ 0)
    (hxd : g * x ^ 2 + B * C = A * d) :
    PolynomialTernaryClearedQuaternionRealSplit.{u, v} A (g * B) C ↔
      PolynomialTernaryClearedQuaternionRealSplit.{u, v} B (g * C) d := by
  have hmul : (g * x) ^ 2 + (g * B) * C = A * (g * d) := by
    calc
      (g * x) ^ 2 + (g * B) * C = g * (g * x ^ 2 + B * C) := by ring
      _ = g * (A * d) := by rw [hxd]
      _ = A * (g * d) := by ring
  have hdesc := polynomialTernaryClearedQuaternionRealSplit_descent
    (R := R) (A := A) (B := g * B) (C := C) (x := g * x) (d := g * d)
    hA0 (mul_ne_zero hg0 hB0) hmul
  let φ := algebraMap (Polynomial R) (RatFunc R)
  have hgφ : φ g ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hg0
  have hfactor :
      PolynomialTernaryClearedQuaternionRealSplit.{u, v} (g * B) C (g * d) ↔
        PolynomialTernaryClearedQuaternionRealSplit.{u, v} B (g * C) d := by
    change RatFuncQuaternionRealSplit.{u, v} (φ (-(g * B * C)))
        (φ (-(g * B * (g * d)))) ↔
      RatFuncQuaternionRealSplit.{u, v} (φ (-(B * (g * C)))) (φ (-(B * d)))
    have hfirst : φ (-(g * B * C)) = φ (-(B * (g * C))) := by
      simp [φ, map_mul, map_neg]
      ring
    have hsecond : φ (-(g * B * (g * d))) =
        φ (-(B * d)) * φ g ^ 2 := by
      simp [φ, map_mul, map_neg, pow_two]
      ring
    rw [hfirst, hsecond]
    exact ratFuncQuaternionRealSplit_mul_square_right hgφ
  exact hdesc.trans hfactor

theorem polynomialTernaryClearedQuaternion_square_part_gcd_normalization
    [Field R] {A B C d x : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0) (hd0 : d ≠ 0)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hBC : IsCoprime B C)
    (hwhole : PolynomialLegendreWholeModConditions A B C)
    (hxd : x ^ 2 + B * C = A * d) :
    ∃ (g q x₀ B₀ d₀ x₁ B₁ d₁ : Polynomial R),
      g ≠ 0 ∧ q ≠ 0 ∧ Squarefree g ∧
      B = q ^ 2 * B₀ ∧ d = q ^ 2 * d₀ ∧ x = q * x₀ ∧
      x₀ ^ 2 + B₀ * C = A * d₀ ∧
      B₀ = g * B₁ ∧ d₀ = g * d₁ ∧
      g * x₁ ^ 2 + B₁ * C = A * d₁ ∧
      IsCoprime B₁ d₁ ∧
      PolynomialLegendreWholeModConditions B₁ (g * C) d₁ ∧
      (PolynomialTernaryClearedQuaternionSplit A B C ↔
        PolynomialTernaryClearedQuaternionSplit B₁ (g * C) d₁) ∧
      (PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
        PolynomialTernaryClearedQuaternionRealSplit.{u, v} B₁ (g * C) d₁) ∧
      B₁.natDegree + (g * C).natDegree + d₁.natDegree + g.natDegree +
          4 * q.natDegree = B.natDegree + C.natDegree + d.natDegree ∧
      (¬ IsUnit (g * q ^ 2) →
        B₁.natDegree + (g * C).natDegree + d₁.natDegree <
          B.natDegree + C.natDegree + d.natDegree) := by
  classical
  let s : Polynomial R := EuclideanDomain.gcd B d
  have hsB : s ∣ B := by
    simpa [s] using EuclideanDomain.gcd_dvd_left B d
  have hs0 : s ≠ 0 := ne_zero_of_dvd_ne_zero hB0 hsB
  rcases exists_squarefree_mul_square_of_ne_zero hs0 with
    ⟨g, q, hg0, hq0, hgsq, hs⟩
  have hq2s : q ^ 2 ∣ s := by
    refine ⟨g, ?_⟩
    simp [hs, mul_comm]
  have hsd : s ∣ d := by
    simpa [s] using EuclideanDomain.gcd_dvd_right B d
  have hq2B : q ^ 2 ∣ B := hq2s.trans hsB
  have hq2d : q ^ 2 ∣ d := hq2s.trans hsd
  rcases hq2B with ⟨B₀, hB⟩
  rcases hq2d with ⟨d₀, hd⟩
  have hq2B' : q ^ 2 ∣ B := ⟨B₀, hB⟩
  have hq2d' : q ^ 2 ∣ d := ⟨d₀, hd⟩
  have hB₀0 : B₀ ≠ 0 := by
    intro hzero
    apply hB0
    rw [hB, hzero]
    simp
  have hd₀0 : d₀ ≠ 0 := by
    intro hzero
    apply hd0
    rw [hd, hzero]
    simp
  have hq2x2 : q ^ 2 ∣ x ^ 2 := by
    have hq2Ad : q ^ 2 ∣ A * d := dvd_mul_of_dvd_right hq2d' A
    have hq2BC : q ^ 2 ∣ B * C := dvd_mul_of_dvd_left hq2B' C
    rw [show x ^ 2 = A * d - B * C by rw [← hxd]; ring]
    exact dvd_sub hq2Ad hq2BC
  have hqx : q ∣ x :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 2) (by norm_num)).mp hq2x2
  rcases hqx with ⟨x₀, hx⟩
  have hidentity : x₀ ^ 2 + B₀ * C = A * d₀ := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hq0)
    calc
      q ^ 2 * (x₀ ^ 2 + B₀ * C) =
          (q * x₀) ^ 2 + (q ^ 2 * B₀) * C := by ring
      _ = x ^ 2 + B * C := by rw [hx, hB]
      _ = A * d := hxd
      _ = q ^ 2 * (A * d₀) := by rw [hd]; ring
  have hqB : q ∣ B :=
    (dvd_pow_self q (by norm_num)).trans hq2B'
  have hAq : IsCoprime A q := hAB.of_isCoprime_of_dvd_right hqB
  have hCq : IsCoprime C q := hBC.symm.of_isCoprime_of_dvd_right hqB
  have hB₀B : B₀ ∣ B := by
    refine ⟨q ^ 2, ?_⟩
    simp [hB, mul_comm]
  have hAB₀ : IsCoprime A B₀ := hAB.of_isCoprime_of_dvd_right hB₀B
  have hB₀C : IsCoprime B₀ C := hBC.of_isCoprime_of_dvd_left hB₀B
  rcases hwhole with ⟨hAmod, hBmod, hCmod⟩
  have hAmodq : IsSquareMod A ((-(B₀ * C)) * q ^ 2) := by
    rw [hB] at hAmod
    simpa [mul_assoc, mul_comm, mul_left_comm, pow_two] using hAmod
  have hAmod₀ : IsSquareMod A (-(B₀ * C)) :=
    IsSquareMod.of_mul_square_of_isCoprime hAq.symm hAmodq
  have hBmod₀ : IsSquareMod B₀ (-(A * C)) := hBmod.of_dvd hB₀B
  have hCmodq : IsSquareMod C ((-(A * B₀)) * q ^ 2) := by
    rw [hB] at hCmod
    simpa [mul_assoc, mul_comm, mul_left_comm, pow_two] using hCmod
  have hCmod₀ : IsSquareMod C (-(A * B₀)) :=
    IsSquareMod.of_mul_square_of_isCoprime hCq.symm hCmodq
  have hwhole₀ : PolynomialLegendreWholeModConditions A B₀ C :=
    ⟨hAmod₀, hBmod₀, hCmod₀⟩
  have hgB₀ : g ∣ B₀ := by
    apply (mul_dvd_mul_iff_left (pow_ne_zero 2 hq0)).mp
    simpa [hs, hB, mul_assoc, mul_comm, mul_left_comm] using hsB
  have hgd₀ : g ∣ d₀ := by
    apply (mul_dvd_mul_iff_left (pow_ne_zero 2 hq0)).mp
    simpa [hs, hd, mul_assoc, mul_comm, mul_left_comm] using hsd
  rcases squareModWitness_common_factor_of_squarefree_factor
      hgsq hgB₀ hgd₀ hidentity with
    ⟨x₁, B₁, d₁, hx₁, hB₁, hd₁, hweighted⟩
  have hB₁0 : B₁ ≠ 0 := by
    intro hzero
    apply hB₀0
    rw [hB₁, hzero]
    simp
  have hd₁0 : d₁ ≠ 0 := by
    intro hzero
    apply hd₀0
    rw [hd₁, hzero]
    simp
  have hB₁d₁rel : IsRelPrime B₁ d₁ := by
    intro D hDB₁ hDd₁
    have hqgD_B : q ^ 2 * (g * D) ∣ B := by
      obtain ⟨t, ht⟩ := hDB₁
      refine ⟨t, ?_⟩
      calc
        B = q ^ 2 * B₀ := hB
        _ = q ^ 2 * (g * B₁) := by rw [← hB₁]
        _ = (q ^ 2 * (g * D)) * t := by rw [ht]; ring
    have hqgD_d : q ^ 2 * (g * D) ∣ d := by
      obtain ⟨t, ht⟩ := hDd₁
      refine ⟨t, ?_⟩
      calc
        d = q ^ 2 * d₀ := hd
        _ = q ^ 2 * (g * d₁) := by rw [← hd₁]
        _ = (q ^ 2 * (g * D)) * t := by rw [ht]; ring
    have hqgD_s : q ^ 2 * (g * D) ∣ s :=
      EuclideanDomain.dvd_gcd hqgD_B hqgD_d
    have hcancel : g * D ∣ g := by
      apply (mul_dvd_mul_iff_left (pow_ne_zero 2 hq0)).mp
      simpa [hs, mul_assoc, mul_comm, mul_left_comm] using hqgD_s
    have hDg : D ∣ 1 := by
      apply (mul_dvd_mul_iff_left hg0).mp
      simpa [mul_comm] using hcancel
    exact isUnit_iff_dvd_one.mpr hDg
  have hB₁d₁ : IsCoprime B₁ d₁ := hB₁d₁rel.isCoprime
  have hsplitq := polynomialTernaryClearedQuaternionSplit_square_factor_transport
    (A := A) (B := B) (C := C) (A' := A) (B' := B₀) (C' := C)
    (a := 1) (b := q) (c := 1) one_ne_zero hq0 one_ne_zero
    (by simp) (by simp [hB, mul_comm]) (by simp)
  have hsplitr0 := polynomialTernaryClearedQuaternionSplit_weighted_descent
    (A := A) (B := B₁) (C := C) (d := d₁) (g := g) (x := x₁)
    hA0 hB₁0 hg0 hweighted
  have hsplit : PolynomialTernaryClearedQuaternionSplit A B C ↔
      PolynomialTernaryClearedQuaternionSplit B₁ (g * C) d₁ :=
    hsplitq.trans (by simpa [hB₁] using hsplitr0)
  have hrealq := polynomialTernaryClearedQuaternionRealSplit_square_factor_transport
    (A := A) (B := B) (C := C) (A' := A) (B' := B₀) (C' := C)
    (a := 1) (b := q) (c := 1) one_ne_zero hq0 one_ne_zero
    (by simp) (by simp [hB, mul_comm]) (by simp)
  have hrealr0 := polynomialTernaryClearedQuaternionRealSplit_weighted_descent
    (R := R) (A := A) (B := B₁) (C := C) (d := d₁) (g := g) (x := x₁)
    hA0 hB₁0 hg0 hweighted
  have hreal : PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
      PolynomialTernaryClearedQuaternionRealSplit.{u, v} B₁ (g * C) d₁ :=
    hrealq.trans (by simpa [hB₁] using hrealr0)
  have hwhole := polynomialLegendreWholeModConditions_common_factor_transport
    (A := A) (B := B₀) (C := C) (g := g) (x₁ := x₁) (B₁ := B₁) (d₁ := d₁)
    hwhole₀ hAB₀ hAC hB₀C hgB₀ hB₁ hweighted hB₁d₁rel.isCoprime
  have hBdeg₀ : B₀.natDegree = g.natDegree + B₁.natDegree := by
    rw [hB₁, Polynomial.natDegree_mul hg0 hB₁0]
  have hddeg₀ : d₀.natDegree = g.natDegree + d₁.natDegree := by
    rw [hd₁, Polynomial.natDegree_mul hg0 hd₁0]
  have hBdeg : B.natDegree = 2 * q.natDegree + B₀.natDegree := by
    simpa [Polynomial.natDegree_mul (pow_ne_zero 2 hq0) hB₀0,
      Polynomial.natDegree_pow] using congrArg Polynomial.natDegree hB
  have hddeg : d.natDegree = 2 * q.natDegree + d₀.natDegree := by
    simpa [Polynomial.natDegree_mul (pow_ne_zero 2 hq0) hd₀0,
      Polynomial.natDegree_pow] using congrArg Polynomial.natDegree hd
  have hGCdeg : (g * C).natDegree = g.natDegree + C.natDegree :=
    Polynomial.natDegree_mul hg0 hC0
  have hmeasure :
      B₁.natDegree + (g * C).natDegree + d₁.natDegree + g.natDegree +
          4 * q.natDegree = B.natDegree + C.natDegree + d.natDegree := by
    rw [hBdeg, hddeg, hBdeg₀, hddeg₀, hGCdeg]
    omega
  have hstrict :
      (¬ IsUnit (g * q ^ 2) →
        B₁.natDegree + (g * C).natDegree + d₁.natDegree <
          B.natDegree + C.natDegree + d.natDegree) := by
    intro hsnon
    have hsndeg : (g * q ^ 2).natDegree ≠ 0 := by
      intro hzero
      apply hsnon
      rcases Polynomial.natDegree_eq_zero.mp hzero with ⟨c, hc⟩
      rw [← hc]
      apply Polynomial.isUnit_C.mpr
      apply isUnit_iff_ne_zero.mpr
      intro hc0
      apply mul_ne_zero hg0 (pow_ne_zero 2 hq0)
      simpa [hc0] using hc
    have hsdeg : 0 < (g * q ^ 2).natDegree := Nat.pos_of_ne_zero hsndeg
    have hsdeg' : (g * q ^ 2).natDegree = g.natDegree + 2 * q.natDegree := by
      rw [Polynomial.natDegree_mul hg0 (pow_ne_zero 2 hq0),
        Polynomial.natDegree_pow]
    rw [hBdeg, hddeg, hBdeg₀, hddeg₀, hGCdeg]
    omega
  exact ⟨g, q, x₀, B₀, d₀, x₁, B₁, d₁, hg0, hq0, hgsq, hB, hd, hx,
    hidentity, hB₁, hd₁, hweighted, hB₁d₁, hwhole, hsplit, hreal, hmeasure,
    hstrict⟩

theorem polynomialLegendreWholeModConditions_transport_of_squareMod
    [Field R] {A B C x d : Polynomial R}
    (hwhole : PolynomialLegendreWholeModConditions A B C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C)
    (hd : x ^ 2 + B * C = A * d) :
    PolynomialLegendreWholeModConditions B C d := by
  rcases hwhole with ⟨_hA, hB, hC⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases hB with ⟨y, hy⟩
    rcases hAB with ⟨s, t, hst⟩
    refine ⟨y * x * s, ?_⟩
    have hy' : B ∣ y ^ 2 + A * C := by
      simpa [sub_eq_add_neg] using hy
    have hAinv : B ∣ A * s - 1 := by
      have hident : A * s - 1 = -(t * B) := by
        rw [← hst]
        ring
      rw [hident]
      exact dvd_neg.mpr (dvd_mul_left B t)
    have had : A * d - x ^ 2 = B * C := by
      calc
        A * d - x ^ 2 = (x ^ 2 + B * C) - x ^ 2 := by rw [hd]
        _ = B * C := by ring
    have hds_eq : d - s * x ^ 2 = B * (t * d + s * C) := by
      calc
        d - s * x ^ 2 = (s * A + t * B) * d - s * x ^ 2 := by rw [hst]; simp
        _ = s * (A * d - x ^ 2) + t * B * d := by ring
        _ = s * (B * C) + t * B * d := by rw [had]
        _ = B * (t * d + s * C) := by ring
    have hds : B ∣ d - s * x ^ 2 := ⟨t * d + s * C, hds_eq⟩
    have hterm1 : B ∣ y ^ 2 * x ^ 2 * s ^ 2 + A * C * x ^ 2 * s ^ 2 := by
      have hmul := dvd_mul_of_dvd_left hy' ((x * s) ^ 2)
      convert hmul using 1
      ring
    have hterm2 : B ∣ C * (d - s * x ^ 2) := dvd_mul_of_dvd_right hds C
    have hterm3 : B ∣ C * x ^ 2 * s * (A * s - 1) := by
      have hmul := dvd_mul_of_dvd_left hAinv (C * x ^ 2 * s)
      convert hmul using 1
      ring
    have hsum : B ∣
        (y ^ 2 * x ^ 2 * s ^ 2 + A * C * x ^ 2 * s ^ 2) +
          C * (d - s * x ^ 2) - C * x ^ 2 * s * (A * s - 1) :=
      dvd_sub (dvd_add hterm1 hterm2) hterm3
    convert hsum using 1
    ring
  · rcases hC with ⟨z, hz⟩
    rcases hAC with ⟨s, t, hst⟩
    refine ⟨z * x * s, ?_⟩
    have hz' : C ∣ z ^ 2 + A * B := by
      simpa [sub_eq_add_neg] using hz
    have hAinv : C ∣ A * s - 1 := by
      have hident : A * s - 1 = -(t * C) := by
        rw [← hst]
        ring
      rw [hident]
      exact dvd_neg.mpr (dvd_mul_left C t)
    have had : A * d - x ^ 2 = B * C := by
      calc
        A * d - x ^ 2 = (x ^ 2 + B * C) - x ^ 2 := by rw [hd]
        _ = B * C := by ring
    have hds_eq : d - s * x ^ 2 = C * (t * d + s * B) := by
      calc
        d - s * x ^ 2 = (s * A + t * C) * d - s * x ^ 2 := by rw [hst]; simp
        _ = s * (A * d - x ^ 2) + t * C * d := by ring
        _ = s * (B * C) + t * C * d := by rw [had]
        _ = C * (t * d + s * B) := by ring
    have hds : C ∣ d - s * x ^ 2 := ⟨t * d + s * B, hds_eq⟩
    have hterm1 : C ∣ z ^ 2 * x ^ 2 * s ^ 2 + A * B * x ^ 2 * s ^ 2 := by
      have hmul := dvd_mul_of_dvd_left hz' ((x * s) ^ 2)
      convert hmul using 1
      ring
    have hterm2 : C ∣ B * (d - s * x ^ 2) := dvd_mul_of_dvd_right hds B
    have hterm3 : C ∣ B * x ^ 2 * s * (A * s - 1) := by
      have hmul := dvd_mul_of_dvd_left hAinv (B * x ^ 2 * s)
      convert hmul using 1
      ring
    have hsum : C ∣
        (z ^ 2 * x ^ 2 * s ^ 2 + A * B * x ^ 2 * s ^ 2) +
          B * (d - s * x ^ 2) - B * x ^ 2 * s * (A * s - 1) :=
      dvd_sub (dvd_add hterm1 hterm2) hterm3
    convert hsum using 1
    ring
  · refine ⟨x, ?_⟩
    rw [sub_neg_eq_add, hd]
    exact dvd_mul_left d A

theorem polynomialTernaryClearedQuaternionSplit_descent_with_wholeMod
    [Field R] {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hAdeg : 0 < A.natDegree)
    (hBCdeg : B.natDegree + C.natDegree < 2 * A.natDegree)
    (hwhole : PolynomialLegendreWholeModConditions A B C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) :
    ∃ x d : Polynomial R,
      x ∈ Polynomial.degreeLT R A.natDegree ∧
        x ^ 2 + B * C = A * d ∧
          (d = 0 ∨ d.natDegree < A.natDegree) ∧
            (PolynomialTernaryClearedQuaternionSplit A B C ↔
              PolynomialTernaryClearedQuaternionSplit B C d) ∧
              PolynomialLegendreWholeModConditions B C d := by
  rcases reducedSquareModWitness_of_degree_bound hA0 hAdeg hBCdeg hwhole.1 with
    ⟨x, d, hx, hxd, hdrop⟩
  exact ⟨x, d, hx, hxd, hdrop,
    polynomialTernaryClearedQuaternionSplit_descent hA0 hB0 hxd,
    polynomialLegendreWholeModConditions_transport_of_squareMod hwhole hAB hAC hxd⟩

/-!
The reduced nonzero quotient has a genuinely normalized next-pivot state.
The old first two coefficients are squarefree and pairwise coprime with the
third, while the quotient itself need not be squarefree.  After the left gcd
step, the new pivot `B₁` is squarefree and coprime to both other coefficients;
the next recursive consumer therefore needs no coprimality assumption between
`g * C` and `d₁` at this stage.
-/
end RatFunc

end RatFuncWittLocalGlobal
