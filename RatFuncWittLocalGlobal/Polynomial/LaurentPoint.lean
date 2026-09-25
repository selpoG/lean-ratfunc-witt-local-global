/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Polynomial.Gcd
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.RingTheory.LaurentSeries

/-!
# Laurent-series point realizations

This file contains the concrete Laurent-series homomorphisms used by the
local-global reductions.  The larger `LocalGlobalReduction` file only uses the
abstract interfaces exposed here.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

open scoped LaurentSeries

noncomputable def toLexRingHom (A : Type*) [Semiring A] : A →+* Lex A where
  toFun := toLex
  map_zero' := rfl
  map_one' := rfl
  map_add' := by
    intro _ _
    rfl
  map_mul' := by
    intro _ _
    rfl

theorem laurentSeries_leadingCoeff_eq_coeff_zero_of_no_negative
    {R : Type u} [Zero R] {f : LaurentSeries R}
    (hneg : ∀ i : ℤ, i < 0 → f.coeff i = 0) (h0 : f.coeff 0 ≠ 0) :
    f.leadingCoeff = f.coeff 0 := by
  have hmem : (0 : ℤ) ∈ f.support :=
    (HahnSeries.mem_support _ _).mpr h0
  have htop : f.orderTop = (0 : ℤ) := by
    refine HahnSeries.orderTop_eq_of_le hmem ?_
    intro g hg
    by_contra hnot
    have hglt : g < 0 := lt_of_not_ge hnot
    exact (HahnSeries.mem_support _ _).mp hg (hneg g hglt)
  have hfne : f ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h0
  rw [HahnSeries.leadingCoeff_of_ne_zero hfne]
  have huntop :
      f.orderTop.untop (HahnSeries.orderTop_ne_top.mpr hfne) = (0 : ℤ) :=
    (WithTop.untop_eq_iff _).mpr htop
  rw [huntop]

theorem scaledShiftedPolynomial_laurentSeries_coeff_zero
    {R : Type u} [Field R] (x ε : R) (p : Polynomial R) :
    (algebraMap (Polynomial R) (LaurentSeries R)
        (p.comp (Polynomial.C ε * Polynomial.X + Polynomial.C x))).coeff 0 = p.eval x := by
  calc
    (algebraMap (Polynomial R) (LaurentSeries R)
        (p.comp (Polynomial.C ε * Polynomial.X + Polynomial.C x))).coeff 0
        = (p.comp (Polynomial.C ε * Polynomial.X + Polynomial.C x)).coeff 0 := by
          rw [show algebraMap (Polynomial R) (LaurentSeries R)
                (p.comp (Polynomial.C ε * Polynomial.X + Polynomial.C x)) =
              (↑(p.comp (Polynomial.C ε * Polynomial.X + Polynomial.C x)) : PowerSeries R) from rfl]
          simpa using
            (HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (R := R)
              (↑(p.comp (Polynomial.C ε * Polynomial.X + Polynomial.C x)) :
                PowerSeries R) 0)
    _ = p.eval x := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simp [Polynomial.eval_comp]

theorem scaledShiftedPolynomial_laurentSeries_coeff_neg
    {R : Type u} [Field R] (x ε : R) (p : Polynomial R) :
    ∀ i : ℤ, i < 0 →
      (algebraMap (Polynomial R) (LaurentSeries R)
          (p.comp (Polynomial.C ε * Polynomial.X + Polynomial.C x))).coeff i = 0 := by
  intro i hi
  rw [show algebraMap (Polynomial R) (LaurentSeries R)
        (p.comp (Polynomial.C ε * Polynomial.X + Polynomial.C x)) =
      (↑(p.comp (Polynomial.C ε * Polynomial.X + Polynomial.C x)) : PowerSeries R) from rfl]
  rw [PowerSeries.coeff_coe]
  simp [hi]

theorem scaledShiftedPolynomial_laurentSeries_leadingCoeff
    {R : Type u} [Field R] {x ε : R} {p : Polynomial R} (hp : p.eval x ≠ 0) :
    (algebraMap (Polynomial R) (LaurentSeries R)
        (p.comp (Polynomial.C ε * Polynomial.X + Polynomial.C x))).leadingCoeff = p.eval x := by
  refine laurentSeries_leadingCoeff_eq_coeff_zero_of_no_negative
    (scaledShiftedPolynomial_laurentSeries_coeff_neg x ε p) ?_ |>.trans
      (scaledShiftedPolynomial_laurentSeries_coeff_zero x ε p)
  rwa [scaledShiftedPolynomial_laurentSeries_coeff_zero]

/--
After reversing coefficients and substituting a nonzero scalar multiple of the
Laurent parameter, the leading coefficient is the original polynomial leading
coefficient.  This is the local piece used for the orderings at infinity, where
`p(X)` is analyzed as `X ^ p.natDegree * p.reverse (X⁻¹)`.
-/
theorem scaledReversePolynomial_laurentSeries_leadingCoeff
    {R : Type u} [Field R] {ε : R} {p : Polynomial R}
    (_hε : ε ≠ 0) (hp : p ≠ 0) :
    (algebraMap (Polynomial R) (LaurentSeries R)
        (p.reverse.comp (Polynomial.C ε * Polynomial.X))).leadingCoeff =
      p.leadingCoeff := by
  have hrev_eval : p.reverse.eval 0 = p.leadingCoeff := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
  have hrev0 : p.reverse.eval 0 ≠ 0 := by
    rw [hrev_eval]
    exact mt Polynomial.leadingCoeff_eq_zero.1 hp
  have hlead :=
    scaledShiftedPolynomial_laurentSeries_leadingCoeff
      (x := 0) (ε := ε) (p := p.reverse) hrev0
  simpa [hrev_eval] using hlead

theorem powerSeries_C_mul_X_laurentSeries_leadingCoeff
    {R : Type u} [Field R] (ε : R) :
    ((HahnSeries.ofPowerSeries ℤ R)
      (↑(Polynomial.C ε * Polynomial.X : Polynomial R) : PowerSeries R)).leadingCoeff = ε := by
  rw [show (↑(Polynomial.C ε * Polynomial.X : Polynomial R) : PowerSeries R) =
      PowerSeries.C ε * PowerSeries.X by simp]
  simp [HahnSeries.C_apply, HahnSeries.leadingCoeff_of_single]

/-- The Laurent-series embedding sends `C a * X` to the single term `a X`. -/
theorem algebraMap_C_mul_X_laurentSeries
    {R : Type u} [Field R] (a : R) :
    algebraMap (Polynomial R) (LaurentSeries R) (Polynomial.C a * Polynomial.X) =
      HahnSeries.single (1 : ℤ) a := by
  rw [map_mul]
  simp [HahnSeries.C_apply, HahnSeries.single_mul_single]

/-- Evaluating a polynomial at a single Laurent monomial is substitution by `C a * X`. -/
theorem polynomial_eval₂_single_one_eq_algebraMap_comp_C_mul_X
    {R : Type u} [Field R] (a : R) (p : Polynomial R) :
    Polynomial.eval₂ (algebraMap R (LaurentSeries R))
        (HahnSeries.single (1 : ℤ) a) p =
      algebraMap (Polynomial R) (LaurentSeries R)
        (p.comp (Polynomial.C a * Polynomial.X)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.add_comp, map_add, Polynomial.eval₂_add, hp, hq]
  | monomial n b =>
      rw [Polynomial.monomial_comp, Polynomial.eval₂_monomial, map_mul, map_pow,
        algebraMap_C_mul_X_laurentSeries]
      rw [HahnSeries.single_pow]
      rw [LaurentSeries.algebraMap_apply]
      rw [Polynomial.algebraMap_hahnSeries_apply]
      rw [show (↑(Polynomial.C b : Polynomial R) : PowerSeries R) = PowerSeries.C b by simp]
      rw [HahnSeries.ofPowerSeries_C]

/--
Evaluating a polynomial at the inverse Laurent parameter reads the polynomial
leading coefficient as the leading coefficient of the resulting Laurent series.
-/
theorem polynomial_eval_single_neg_one_laurentSeries_leadingCoeff
    {R : Type u} [Field R] {ε : R} (hε : ε ≠ 0) {p : Polynomial R} (hp : p ≠ 0) :
    (Polynomial.eval₂ (algebraMap R (LaurentSeries R))
        (HahnSeries.single (-1 : ℤ) ε) p).leadingCoeff =
      p.leadingCoeff * ε ^ p.natDegree := by
  let x : LaurentSeries R := HahnSeries.single (-1 : ℤ) ε
  have hx : x ≠ 0 := HahnSeries.single_ne_zero hε
  let _ : Invertible x := invertibleOfNonzero hx
  have hformula :=
    Polynomial.eval₂_reverse_mul_pow (algebraMap R (LaurentSeries R)) x p
  have hfirst :
      (Polynomial.eval₂ (algebraMap R (LaurentSeries R)) (⅟x) p.reverse).leadingCoeff =
        p.leadingCoeff := by
    have hinv : ⅟x = HahnSeries.single (1 : ℤ) ε⁻¹ := by
      dsimp [x]
      rw [invOf_eq_inv]
      simp
    rw [hinv]
    rw [polynomial_eval₂_single_one_eq_algebraMap_comp_C_mul_X]
    exact scaledReversePolynomial_laurentSeries_leadingCoeff
      (ε := ε⁻¹) (p := p) (inv_ne_zero hε) hp
  have hsecond : (x ^ p.natDegree).leadingCoeff = ε ^ p.natDegree := by
    dsimp [x]
    rw [HahnSeries.single_pow, HahnSeries.leadingCoeff_of_single]
  rw [← hformula]
  rw [HahnSeries.leadingCoeff_mul, hfirst, hsecond]

/-- The `+∞` Laurent evaluation sends positive leading coefficient to positivity. -/
theorem polynomial_posInfinity_eval_pos_laurentSeries
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {p : Polynomial R} (hp : 0 < p.leadingCoeff) :
    0 < toLex (Polynomial.eval₂ (algebraMap R (LaurentSeries R))
      (HahnSeries.single (-1 : ℤ) (1 : R)) p) := by
  refine HahnSeries.leadingCoeff_pos_iff.mp ?_
  have hp0 : p ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.2 hp.ne'
  rw [ofLex_toLex]
  rw [polynomial_eval_single_neg_one_laurentSeries_leadingCoeff
    (ε := (1 : R)) one_ne_zero hp0]
  simpa using hp

/-- The `+∞` Laurent evaluation sends negative leading coefficient to negativity. -/
theorem polynomial_posInfinity_eval_neg_laurentSeries
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {p : Polynomial R} (hp : p.leadingCoeff < 0) :
    toLex (Polynomial.eval₂ (algebraMap R (LaurentSeries R))
      (HahnSeries.single (-1 : ℤ) (1 : R)) p) < 0 := by
  refine HahnSeries.leadingCoeff_neg_iff.mp ?_
  have hp0 : p ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.2 hp.ne
  rw [ofLex_toLex]
  rw [polynomial_eval_single_neg_one_laurentSeries_leadingCoeff
    (ε := (1 : R)) one_ne_zero hp0]
  simpa using hp

/-- The `-∞` Laurent evaluation sends the parity-adjusted positive sign to positivity. -/
theorem polynomial_negInfinity_eval_pos_laurentSeries
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {p : Polynomial R}
    (hp : (Even p.natDegree ∧ 0 < p.leadingCoeff) ∨
      (Odd p.natDegree ∧ p.leadingCoeff < 0)) :
    0 < toLex (Polynomial.eval₂ (algebraMap R (LaurentSeries R))
      (HahnSeries.single (-1 : ℤ) (-1 : R)) p) := by
  refine HahnSeries.leadingCoeff_pos_iff.mp ?_
  have hp0 : p ≠ 0 := by
    rcases hp with ⟨_, hlc⟩ | ⟨_, hlc⟩
    · exact mt Polynomial.leadingCoeff_eq_zero.2 hlc.ne'
    · exact mt Polynomial.leadingCoeff_eq_zero.2 hlc.ne
  rw [ofLex_toLex]
  rw [polynomial_eval_single_neg_one_laurentSeries_leadingCoeff
    (ε := (-1 : R)) (neg_ne_zero.mpr one_ne_zero) hp0]
  rcases hp with ⟨hdeg, hlc⟩ | ⟨hdeg, hlc⟩
  · rw [hdeg.neg_one_pow]
    simpa using hlc
  · rw [hdeg.neg_one_pow, mul_neg_one]
    exact neg_pos.mpr hlc

/-- The `-∞` Laurent evaluation sends the parity-adjusted negative sign to negativity. -/
theorem polynomial_negInfinity_eval_neg_laurentSeries
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {p : Polynomial R}
    (hp : (Even p.natDegree ∧ p.leadingCoeff < 0) ∨
      (Odd p.natDegree ∧ 0 < p.leadingCoeff)) :
    toLex (Polynomial.eval₂ (algebraMap R (LaurentSeries R))
      (HahnSeries.single (-1 : ℤ) (-1 : R)) p) < 0 := by
  refine HahnSeries.leadingCoeff_neg_iff.mp ?_
  have hp0 : p ≠ 0 := by
    rcases hp with ⟨_, hlc⟩ | ⟨_, hlc⟩
    · exact mt Polynomial.leadingCoeff_eq_zero.2 hlc.ne
    · exact mt Polynomial.leadingCoeff_eq_zero.2 hlc.ne'
  rw [ofLex_toLex]
  rw [polynomial_eval_single_neg_one_laurentSeries_leadingCoeff
    (ε := (-1 : R)) (neg_ne_zero.mpr one_ne_zero) hp0]
  rcases hp with ⟨hdeg, hlc⟩ | ⟨hdeg, hlc⟩
  · rw [hdeg.neg_one_pow]
    simpa using hlc
  · rw [hdeg.neg_one_pow, mul_neg_one]
    exact neg_lt_zero.mpr hlc

theorem scaledShiftedPolynomial_mul_X_sub_C_laurentSeries_leadingCoeff
    {R : Type u} [Field R] {x ε : R} {p : Polynomial R} (hp : p.eval x ≠ 0) :
    (algebraMap (Polynomial R) (LaurentSeries R)
        ((p * (Polynomial.X - Polynomial.C x)).comp
          (Polynomial.C ε * Polynomial.X + Polynomial.C x))).leadingCoeff =
      p.eval x * ε := by
  let shift : Polynomial R := Polynomial.C ε * Polynomial.X + Polynomial.C x
  let lhs : LaurentSeries R :=
    algebraMap (Polynomial R) (LaurentSeries R)
      ((p * (Polynomial.X - Polynomial.C x)).comp shift)
  let A : LaurentSeries R :=
    algebraMap (Polynomial R) (LaurentSeries R) (p.comp shift)
  let L : LaurentSeries R :=
    algebraMap (Polynomial R) (LaurentSeries R) (Polynomial.C ε * Polynomial.X)
  have hcomp :
      (p * (Polynomial.X - Polynomial.C x)).comp shift =
        (p.comp shift) * (Polynomial.C ε * Polynomial.X) := by
    rw [Polynomial.mul_comp]
    congr 1
    simp [shift, Polynomial.sub_comp]
  have hlhs : lhs = A * L := by
    dsimp [lhs, A, L]
    rw [hcomp]
    simp
  have hA : A.leadingCoeff = p.eval x := by
    dsimp [A, shift]
    exact scaledShiftedPolynomial_laurentSeries_leadingCoeff (x := x) (ε := ε) (p := p) hp
  have hL : L.leadingCoeff = ε := by
    dsimp [L]
    exact powerSeries_C_mul_X_laurentSeries_leadingCoeff ε
  change lhs.leadingCoeff = p.eval x * ε
  rw [hlhs, HahnSeries.leadingCoeff_mul, hA, hL]

theorem scaledShifted_X_sub_C_mul_polynomial_laurentSeries_leadingCoeff
    {R : Type u} [Field R] {x ε : R} {p : Polynomial R} (hp : p.eval x ≠ 0) :
    (algebraMap (Polynomial R) (LaurentSeries R)
        (((Polynomial.X - Polynomial.C x) * p).comp
          (Polynomial.C ε * Polynomial.X + Polynomial.C x))).leadingCoeff =
      p.eval x * ε := by
  rw [mul_comm (Polynomial.X - Polynomial.C x) p]
  exact scaledShiftedPolynomial_mul_X_sub_C_laurentSeries_leadingCoeff
    (x := x) (ε := ε) (p := p) hp

theorem scaledLinearFactorAndPointHomPos_laurentSeries
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {x : R} {B C q : Polynomial R}
    (hB : 0 < B.eval x) (hC : C = q * (Polynomial.X - Polynomial.C x))
    (hq : q.eval x ≠ 0) :
    ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K),
      ∃ f : RatFunc R →+* K,
        0 < f (algebraMap (Polynomial R) (RatFunc R) B) ∧
          0 < f (algebraMap (Polynomial R) (RatFunc R) C) := by
  let ε : R := q.eval x
  have hε : ε ≠ 0 := by
    simpa [ε] using hq
  let shift : Polynomial R := Polynomial.C ε * Polynomial.X + Polynomial.C x
  let φpoly : Polynomial R →+* Polynomial R := Polynomial.compRingHom shift
  let φlaur : Polynomial R →+* LaurentSeries R :=
    (algebraMap (Polynomial R) (LaurentSeries R)).comp φpoly
  let φ : Polynomial R →+* Lex (LaurentSeries R) :=
    (toLexRingHom (LaurentSeries R)).comp φlaur
  have hφ_apply (p : Polynomial R) :
      ofLex (φ p) =
        algebraMap (Polynomial R) (LaurentSeries R) (p.comp shift) := by
    rfl
  have hshift_not_const : shift ≠ Polynomial.C (shift.coeff 0) := by
    intro hshift
    have hcoeff := congrArg (fun p : Polynomial R => p.coeff 1) hshift
    have hcoeff' : ε = 0 := by
      simpa [shift] using hcoeff
    exact hε hcoeff'
  have hφ : nonZeroDivisors (Polynomial R) ≤
      (nonZeroDivisors (Lex (LaurentSeries R))).comap φ := by
    intro p hp
    rw [Submonoid.mem_comap]
    refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
    intro hzero
    have hcomp_zero : p.comp shift = 0 := by
      apply FaithfulSMul.algebraMap_injective (Polynomial R) (LaurentSeries R)
      apply_fun ofLex at hzero
      simpa [φ, φlaur, φpoly, shift] using hzero
    have hpzero : p = 0 := by
      have hz := (Polynomial.comp_eq_zero_iff.mp hcomp_zero)
      rcases hz with hpzero | hbad
      · exact hpzero
      · exact False.elim (hshift_not_const hbad.2)
    exact nonZeroDivisors.ne_zero hp hpzero
  let f : RatFunc R →+* Lex (LaurentSeries R) := RatFunc.liftRingHom φ hφ
  refine ⟨Lex (LaurentSeries R), inferInstance, inferInstance, inferInstance, f, ?_, ?_⟩
  · have hmap :
        f (algebraMap (Polynomial R) (RatFunc R) B) = φ B := by
      exact RatFunc.liftRingHom_algebraMap φ hφ _
    have hpos : 0 < φ B := by
      refine HahnSeries.leadingCoeff_pos_iff.mp ?_
      have hlead : (ofLex (φ B)).leadingCoeff = B.eval x := by
        rw [hφ_apply]
        simpa only [shift] using scaledShiftedPolynomial_laurentSeries_leadingCoeff
          (x := x) (ε := ε) (p := B) hB.ne'
      rw [hlead]
      exact hB
    exact hmap.symm ▸ hpos
  · have hmap :
        f (algebraMap (Polynomial R) (RatFunc R) C) = φ C := by
      exact RatFunc.liftRingHom_algebraMap φ hφ _
    have hpos : 0 < φ C := by
      refine HahnSeries.leadingCoeff_pos_iff.mp ?_
      have hlead : (ofLex (φ C)).leadingCoeff = q.eval x * ε := by
        rw [hφ_apply, hC]
        simpa only [shift] using
          scaledShiftedPolynomial_mul_X_sub_C_laurentSeries_leadingCoeff
          (x := x) (ε := ε) (p := q) hq
      rw [hlead]
      dsimp [ε]
      exact mul_self_pos.mpr hq
    exact hmap.symm ▸ hpos

theorem scaledLinearFactorPairHomPos_laurentSeries
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {x : R} {B C qB qC : Polynomial R}
    (hB : B = qB * (Polynomial.X - Polynomial.C x))
    (hC : C = qC * (Polynomial.X - Polynomial.C x))
    (hprod : 0 < qB.eval x * qC.eval x) :
    ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K),
      ∃ f : RatFunc R →+* K,
        0 < f (algebraMap (Polynomial R) (RatFunc R) B) ∧
          0 < f (algebraMap (Polynomial R) (RatFunc R) C) := by
  have hmul_ne : qB.eval x * qC.eval x ≠ 0 := ne_of_gt hprod
  have hqB : qB.eval x ≠ 0 := (mul_ne_zero_iff.mp hmul_ne).1
  have hqC : qC.eval x ≠ 0 := (mul_ne_zero_iff.mp hmul_ne).2
  let ε : R := qB.eval x
  have hε : ε ≠ 0 := by
    simpa [ε] using hqB
  let shift : Polynomial R := Polynomial.C ε * Polynomial.X + Polynomial.C x
  let φpoly : Polynomial R →+* Polynomial R := Polynomial.compRingHom shift
  let φlaur : Polynomial R →+* LaurentSeries R :=
    (algebraMap (Polynomial R) (LaurentSeries R)).comp φpoly
  let φ : Polynomial R →+* Lex (LaurentSeries R) :=
    (toLexRingHom (LaurentSeries R)).comp φlaur
  have hφ_apply (p : Polynomial R) :
      ofLex (φ p) =
        algebraMap (Polynomial R) (LaurentSeries R) (p.comp shift) := by
    rfl
  have hshift_not_const : shift ≠ Polynomial.C (shift.coeff 0) := by
    intro hshift
    have hcoeff := congrArg (fun p : Polynomial R => p.coeff 1) hshift
    have hcoeff' : ε = 0 := by
      simpa [shift] using hcoeff
    exact hε hcoeff'
  have hφ : nonZeroDivisors (Polynomial R) ≤
      (nonZeroDivisors (Lex (LaurentSeries R))).comap φ := by
    intro p hp
    rw [Submonoid.mem_comap]
    refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
    intro hzero
    have hcomp_zero : p.comp shift = 0 := by
      apply FaithfulSMul.algebraMap_injective (Polynomial R) (LaurentSeries R)
      apply_fun ofLex at hzero
      simpa [φ, φlaur, φpoly, shift] using hzero
    have hpzero : p = 0 := by
      have hz := (Polynomial.comp_eq_zero_iff.mp hcomp_zero)
      rcases hz with hpzero | hbad
      · exact hpzero
      · exact False.elim (hshift_not_const hbad.2)
    exact nonZeroDivisors.ne_zero hp hpzero
  let f : RatFunc R →+* Lex (LaurentSeries R) := RatFunc.liftRingHom φ hφ
  refine ⟨Lex (LaurentSeries R), inferInstance, inferInstance, inferInstance, f, ?_, ?_⟩
  · have hmap :
        f (algebraMap (Polynomial R) (RatFunc R) B) = φ B := by
      exact RatFunc.liftRingHom_algebraMap φ hφ _
    have hpos : 0 < φ B := by
      refine HahnSeries.leadingCoeff_pos_iff.mp ?_
      have hlead : (ofLex (φ B)).leadingCoeff = qB.eval x * ε := by
        rw [hφ_apply, hB]
        simpa only [shift] using
          scaledShiftedPolynomial_mul_X_sub_C_laurentSeries_leadingCoeff
          (x := x) (ε := ε) (p := qB) hqB
      rw [hlead]
      dsimp [ε]
      exact mul_self_pos.mpr hqB
    exact hmap.symm ▸ hpos
  · have hmap :
        f (algebraMap (Polynomial R) (RatFunc R) C) = φ C := by
      exact RatFunc.liftRingHom_algebraMap φ hφ _
    have hpos : 0 < φ C := by
      refine HahnSeries.leadingCoeff_pos_iff.mp ?_
      have hlead : (ofLex (φ C)).leadingCoeff = qC.eval x * ε := by
        rw [hφ_apply, hC]
        simpa only [shift] using
          scaledShiftedPolynomial_mul_X_sub_C_laurentSeries_leadingCoeff
          (x := x) (ε := ε) (p := qC) hqC
      rw [hlead]
      dsimp [ε]
      simpa [mul_comm] using hprod
    exact hmap.symm ▸ hpos

theorem squarefreeGcdSplit_homPos_of_C₁_linear_laurentSeries
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {B C π : Polynomial R} {a : R} (s : SquarefreeGcdSplit B C)
    (hCsq : Squarefree C) (hπ : Irreducible π) (hπC₁ : π ∣ s.C₁)
    (hlin : Associated π (Polynomial.X - Polynomial.C a)) (hBpos : 0 < B.eval a) :
    ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K),
      ∃ f : RatFunc R →+* K,
        0 < f (algebraMap (Polynomial R) (RatFunc R) B) ∧
          0 < f (algebraMap (Polynomial R) (RatFunc R) C) := by
  let lin : Polynomial R := Polynomial.X - Polynomial.C a
  let q : Polynomial R := C /ₘ lin
  have hroot : C.IsRoot a := s.isRoot_C_of_irreducible_dvd_C₁_of_linear hπ hπC₁ hlin
  have hCeq : C = q * lin := by
    have hmul : lin * q = C := by
      exact (Polynomial.mul_divByMonic_eq_iff_isRoot (p := C) (a := a)).mpr hroot
    rw [← hmul, mul_comm]
  have hq : q.eval a ≠ 0 := by
    dsimp [q, lin]
    exact eval_divByMonic_X_sub_C_ne_zero_of_squarefree_of_isRoot hCsq hroot
  exact scaledLinearFactorAndPointHomPos_laurentSeries
    (x := a) (B := B) (C := C) (q := q) hBpos hCeq hq

theorem squarefreeGcdSplit_homPos_of_B₁_linear_laurentSeries
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {B C π : Polynomial R} {a : R} (s : SquarefreeGcdSplit B C)
    (hBsq : Squarefree B) (hπ : Irreducible π) (hπB₁ : π ∣ s.B₁)
    (hlin : Associated π (Polynomial.X - Polynomial.C a)) (hCpos : 0 < C.eval a) :
    ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K),
      ∃ f : RatFunc R →+* K,
        0 < f (algebraMap (Polynomial R) (RatFunc R) B) ∧
          0 < f (algebraMap (Polynomial R) (RatFunc R) C) := by
  let lin : Polynomial R := Polynomial.X - Polynomial.C a
  let q : Polynomial R := B /ₘ lin
  have hroot : B.IsRoot a := s.isRoot_B_of_irreducible_dvd_B₁_of_linear hπ hπB₁ hlin
  have hBeq : B = q * lin := by
    have hmul : lin * q = B := by
      exact (Polynomial.mul_divByMonic_eq_iff_isRoot (p := B) (a := a)).mpr hroot
    rw [← hmul, mul_comm]
  have hq : q.eval a ≠ 0 := by
    dsimp [q, lin]
    exact eval_divByMonic_X_sub_C_ne_zero_of_squarefree_of_isRoot hBsq hroot
  rcases scaledLinearFactorAndPointHomPos_laurentSeries
      (x := a) (B := C) (C := B) (q := q) hCpos hBeq hq with
    ⟨K, hKfield, hKorder, hKstrict, f, hCpos', hBpos'⟩
  exact ⟨K, hKfield, hKorder, hKstrict, f, hBpos', hCpos'⟩

theorem squarefreeGcdSplit_homPos_of_G_linear_laurentSeries
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {B C π : Polynomial R} {a : R} (s : SquarefreeGcdSplit B C)
    (_hπ : Irreducible π) (hπG : π ∣ s.G)
    (hlin : Associated π (Polynomial.X - Polynomial.C a))
    (hprod : 0 < (s.C₁ * s.B₁).eval a) :
    ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K),
      ∃ f : RatFunc R →+* K,
        0 < f (algebraMap (Polynomial R) (RatFunc R) B) ∧
          0 < f (algebraMap (Polynomial R) (RatFunc R) C) := by
  let lin : Polynomial R := Polynomial.X - Polynomial.C a
  let qG : Polynomial R := s.G /ₘ lin
  let qB : Polynomial R := qG * s.B₁
  let qC : Polynomial R := qG * s.C₁
  have hlinear : lin ∣ s.G := by
    dsimp [lin]
    exact hlin.dvd'.trans hπG
  have hGroot : s.G.IsRoot a := by
    dsimp [lin] at hlinear
    exact Polynomial.dvd_iff_isRoot.mp hlinear
  have hGmul : lin * qG = s.G := by
    dsimp [qG, lin]
    exact (Polynomial.mul_divByMonic_eq_iff_isRoot (p := s.G) (a := a)).mpr hGroot
  have hqG : qG.eval a ≠ 0 := by
    dsimp [qG, lin]
    exact eval_divByMonic_X_sub_C_ne_zero_of_squarefree_of_isRoot s.squarefree_G hGroot
  have hB : B = qB * lin := by
    calc
      B = s.G * s.B₁ := s.hB
      _ = (lin * qG) * s.B₁ := by rw [hGmul]
      _ = qB * lin := by ring
  have hC : C = qC * lin := by
    calc
      C = s.G * s.C₁ := s.hC
      _ = (lin * qG) * s.C₁ := by rw [hGmul]
      _ = qC * lin := by ring
  have hquotprod : 0 < qB.eval a * qC.eval a := by
    have hqGsq : 0 < qG.eval a * qG.eval a := mul_self_pos.mpr hqG
    have hB₁C₁ : 0 < s.B₁.eval a * s.C₁.eval a := by
      simpa [Polynomial.eval_mul, mul_comm] using hprod
    have hmain : 0 < (qG.eval a * qG.eval a) * (s.B₁.eval a * s.C₁.eval a) :=
      mul_pos hqGsq hB₁C₁
    simpa [qB, qC, Polynomial.eval_mul, mul_comm, mul_left_comm, mul_assoc] using hmain
  exact scaledLinearFactorPairHomPos_laurentSeries
    (x := a) (B := B) (C := C) (qB := qB) (qC := qC) hB hC hquotprod

/--
Field-hom version of the linear root principles.  This is weaker and closer to
the concrete local construction than an ordered `RatFunc` construction: it is
enough to send `RatFunc R` to some ordered field where the original binary
coefficients are both positive.
-/
def SquarefreeGcdLegendreLinearRootHomPosPrinciples
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    Prop :=
  ∀ B C : Polynomial R,
    B ≠ 0 →
      C ≠ 0 →
        Squarefree B →
          Squarefree C →
            ∀ s : SquarefreeGcdSplit B C,
              (∀ π : Polynomial R, ∀ a : R,
                Irreducible π → π ∣ s.G →
                  Associated π (Polynomial.X - Polynomial.C a) →
                    0 < (s.C₁ * s.B₁).eval a →
                      ∃ (K : Type v) (_ : Field K) (_ : LinearOrder K)
                        (_ : IsStrictOrderedRing K),
                        ∃ f : RatFunc R →+* K,
                          0 < f (algebraMap (Polynomial R) (RatFunc R) B) ∧
                            0 < f (algebraMap (Polynomial R) (RatFunc R) C)) ∧
                (∀ π : Polynomial R, ∀ a : R,
                  Irreducible π → π ∣ s.C₁ →
                    Associated π (Polynomial.X - Polynomial.C a) →
                      0 < B.eval a →
                        ∃ (K : Type v) (_ : Field K) (_ : LinearOrder K)
                          (_ : IsStrictOrderedRing K),
                          ∃ f : RatFunc R →+* K,
                            0 < f (algebraMap (Polynomial R) (RatFunc R) B) ∧
                              0 < f (algebraMap (Polynomial R) (RatFunc R) C)) ∧
                  (∀ π : Polynomial R, ∀ a : R,
                    Irreducible π → π ∣ s.B₁ →
                      Associated π (Polynomial.X - Polynomial.C a) →
                        0 < C.eval a →
                          ∃ (K : Type v) (_ : Field K) (_ : LinearOrder K)
                            (_ : IsStrictOrderedRing K),
                            ∃ f : RatFunc R →+* K,
                              0 < f (algebraMap (Polynomial R) (RatFunc R) B) ∧
                                0 < f (algebraMap (Polynomial R) (RatFunc R) C))

theorem squarefreeGcdLegendreLinearRootHomPosPrinciples_laurentSeries
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    SquarefreeGcdLegendreLinearRootHomPosPrinciples.{u, u} R := by
  intro B C _hB0 _hC0 hBsq hCsq s
  refine ⟨?_, ?_, ?_⟩
  · intro π a hπ hπG hlin hpos
    exact squarefreeGcdSplit_homPos_of_G_linear_laurentSeries
      (s := s) hπ hπG hlin hpos
  · intro π a hπ hπC₁ hlin hpos
    exact squarefreeGcdSplit_homPos_of_C₁_linear_laurentSeries
      (s := s) hCsq hπ hπC₁ hlin hpos
  · intro π a hπ hπB₁ hlin hpos
    exact squarefreeGcdSplit_homPos_of_B₁_linear_laurentSeries
      (s := s) hBsq hπ hπB₁ hlin hpos

end RatFunc

end RatFuncWittLocalGlobal
