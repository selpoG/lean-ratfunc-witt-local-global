/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Ordering.Obstruction
import RatFuncWittLocalGlobal.Polynomial.NormalForms
import RatFuncWittLocalGlobal.Polynomial.RatFuncReduction
import RatFuncWittLocalGlobal.Polynomial.Gcd
import RatFuncWittLocalGlobal.Polynomial.LaurentPoint
import RatFuncWittLocalGlobal.Polynomial.Positivity
import RatFuncWittLocalGlobal.Polynomial.LegendreLinearAlgebra.Coefficients
import RatFuncWittLocalGlobal.Polynomial.LegendreLinearAlgebra.Remainders
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import Mathlib.Topology.Algebra.Polynomial

/-!
# Residue fields of nonlinear irreducible polynomials

This module contains the residue-quotient and standard complexification
lemmas used to discharge nonlinear irreducible-factor square conditions.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

/--
The nonlinear irreducible-factor input expected over a real closed field:
every element is square modulo every non-linear irreducible polynomial.
-/
def NonlinearIrreducibleDivisorSquareMod
    (R : Type u) [Field R] : Prop :=
  ∀ π f : Polynomial R,
    Irreducible π → π.natDegree ≠ 1 → IsSquareMod π f

/--
The quotient-ring version of the nonlinear irreducible-factor input.  It is
often easier to prove square roots in the residue quotient and then return to
`IsSquareMod`.
-/
def NonlinearIrreducibleQuotientSquares
    (R : Type u) [Field R] : Prop :=
  ∀ π f : Polynomial R,
    Irreducible π →
      π.natDegree ≠ 1 →
        IsSquare (Ideal.Quotient.mk (Ideal.span ({π} : Set (Polynomial R))) f)

/--
Degree bound target for irreducible polynomials.  Over a real closed field this
is the usual statement that irreducibles have degree at most two.
-/
def IrreducibleNatDegreeLeTwo
    (R : Type u) [Field R] : Prop :=
  ∀ π : Polynomial R, Irreducible π → π.natDegree ≤ 2

open scoped IntermediateField
/-- A finite extension of a real closed field with odd degree is trivial.

The primitive-element reduction is the part of the Artin--Schreier argument
that is independent of any splitting-field or Galois-group infrastructure.
-/
theorem finiteDimensional_eq_one_of_odd_finrank_realClosed
    {R K : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    [Field K] [Algebra R K] [FiniteDimensional R K]
    (hodd : Odd (Module.finrank R K)) :
    Module.finrank R K = 1 := by
  let α : K := (Field.exists_primitive_element R K).choose
  have hprim : R⟮α⟯ = ⊤ := (Field.exists_primitive_element R K).choose_spec
  have hdeg : (minpoly R α).natDegree = Module.finrank R K :=
    (Field.primitive_element_iff_minpoly_natDegree_eq R α).mp hprim
  have hminirr : Irreducible (minpoly R α) :=
    minpoly.irreducible (Algebra.IsIntegral.isIntegral α)
  have hroot : ∃ x : R, (minpoly R α).IsRoot x :=
    IsRealClosed.exists_isRoot_of_odd_natDegree (R := R) (f := minpoly R α)
      (by simpa [hdeg] using hodd)
  rcases hroot with ⟨x, hx⟩
  have hdeg_one : (minpoly R α).natDegree = 1 := by
    have hdegree : (minpoly R α).degree = 1 :=
      Polynomial.degree_eq_one_of_irreducible_of_root hminirr hx
    exact Polynomial.natDegree_eq_of_degree_eq_some hdegree
  exact hdeg ▸ hdeg_one

/- The Galois group of a finite Galois extension of a real closed field has
   odd-order Sylow complement trivial: its order is therefore a power of two.
   The fixed field of a Sylow-2 subgroup has odd degree, and the preceding
   primitive-element lemma collapses that degree to one. -/
theorem finiteGalois_card_is_two_power_of_realClosed
    {R L : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L] :
    ∃ n : ℕ, Nat.card (Gal(L / R)) = 2 ^ n := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 (Gal(L / R)) := default
  let F : Type _ := IntermediateField.fixedField (P : Subgroup (Gal(L / R)))
  have hmul : Module.finrank R F * Nat.card P = Nat.card (Gal(L / R)) := by
    rw [IsGalois.card_aut_eq_finrank R L,
      ← Module.finrank_mul_finrank R F L,
      IntermediateField.finrank_fixedField_eq_card]
  have hindex : Module.finrank R F = P.index := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card P)
    rw [hmul, P.index_mul_card]
  have hodd : Odd (Module.finrank R F) := by
    rw [hindex]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr P.not_dvd_index).odd_of_left
  have hFone : Module.finrank R F = 1 :=
    finiteDimensional_eq_one_of_odd_finrank_realClosed hodd
  have hindex_one : P.index = 1 := by omega
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  refine ⟨n, ?_⟩
  have hcard : Nat.card (Gal(L / R)) = Nat.card P := by
    rw [← P.index_mul_card, hindex_one, one_mul]
  exact hcard.trans hn

/--
Degree part of the real-closed-field nonlinear irreducible analysis: every
nonlinear irreducible polynomial over `R` has degree two.
-/
def NonlinearIrreducibleNatDegreeTwo
    (R : Type u) [Field R] : Prop :=
  ∀ π : Polynomial R,
    Irreducible π →
      π.natDegree ≠ 1 →
        π.natDegree = 2

theorem nonlinearIrreducibleNatDegreeTwo_of_irreducibleNatDegreeLeTwo
    {R : Type u} [Field R]
    (hle : IrreducibleNatDegreeLeTwo R) :
    NonlinearIrreducibleNatDegreeTwo R := by
  intro π hπ hne_one
  have hpos : 0 < π.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hπ)
  have hle_two : π.natDegree ≤ 2 := hle π hπ
  omega

/--
Square-root part of the quadratic residue analysis: modulo an irreducible
quadratic, every quotient element is a square.
-/
def QuadraticIrreducibleQuotientSquares
    (R : Type u) [Field R] : Prop :=
  ∀ π f : Polynomial R,
    Irreducible π →
      π.natDegree = 2 →
        IsSquare (Ideal.Quotient.mk (Ideal.span ({π} : Set (Polynomial R))) f)

theorem quadraticIrreducibleQuotientSquares_of_realClosed
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    QuadraticIrreducibleQuotientSquares R := by
  intro π f hπ hdeg
  apply isSquare_quotient_span_singleton_of_isSquareMod
  let πm : Polynomial R := π * Polynomial.C π.leadingCoeff⁻¹
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hassoc : Associated πm π := by
    simpa [πm] using associated_mul_leadingCoeff_inv hπ0
  have hmonic : πm.Monic := by
    simpa [πm] using Polynomial.monic_mul_leadingCoeff_inv hπ0
  have hirr_m : Irreducible πm := hassoc.irreducible_iff.mpr hπ
  have hdeg_m : πm.natDegree = 2 := by
    simpa [πm, hdeg] using Polynomial.natDegree_mul_leadingCoeff_inv π hπ0
  exact (isSquareMod_associated_iff hassoc).mp
    (isSquareMod_irreducible_monic_natDegree_two hirr_m hmonic hdeg_m)

theorem irreducible_X_sq_add_one
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    Irreducible (Polynomial.X ^ 2 + Polynomial.C (1 : R) : Polynomial R) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have hdeg :
        (Polynomial.X ^ 2 + Polynomial.C (1 : R) : Polynomial R).natDegree = 2 := by
      simpa using (Polynomial.natDegree_X_pow_add_C (R := R) (n := 2) (r := (1 : R)))
    rw [Finset.mem_Icc, hdeg]
    norm_num
  · intro x hx
    rw [Polynomial.IsRoot] at hx
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hx
    have hpos : 0 < x ^ 2 + 1 :=
      add_pos_of_nonneg_of_pos (sq_nonneg x) (zero_lt_one : (0 : R) < 1)
    exact hpos.ne' hx

noncomputable def standardComplexificationPolynomial
    (R : Type u) [CommRing R] : Polynomial R :=
  Polynomial.X ^ 2 + Polynomial.C (1 : R)

noncomputable def standardComplexificationIdeal
    (R : Type u) [CommRing R] : Ideal (Polynomial R) :=
  Ideal.span ({standardComplexificationPolynomial R} : Set (Polynomial R))

abbrev StandardComplexification
    (R : Type u) [CommRing R] :=
  Polynomial R ⧸ standardComplexificationIdeal R

noncomputable def standardComplexificationI
    (R : Type u) [Field R] : StandardComplexification R :=
  Ideal.Quotient.mk (standardComplexificationIdeal R) Polynomial.X

theorem standardComplexificationI_sq
    (R : Type u) [Field R] :
    standardComplexificationI R ^ 2 = -(1 : StandardComplexification R) := by
  let I : Ideal (Polynomial R) := standardComplexificationIdeal R
  change (Ideal.Quotient.mk I Polynomial.X) ^ 2 = -(1 : Polynomial R ⧸ I)
  rw [← map_pow]
  change Ideal.Quotient.mk I (Polynomial.X ^ 2) =
    Ideal.Quotient.mk I (-(1 : Polynomial R))
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := I) (Polynomial.X ^ 2) (-(1 : Polynomial R))).mpr
  rw [show I = standardComplexificationIdeal R from rfl, standardComplexificationIdeal]
  change Polynomial.X ^ 2 - (-(1 : Polynomial R)) ∈
    Ideal.span ({standardComplexificationPolynomial R} : Set (Polynomial R))
  simp [standardComplexificationPolynomial, sub_neg_eq_add]

theorem standardComplexification_mk_eq_modByMonic
    {R : Type u} [Field R] (p : Polynomial R) :
    Ideal.Quotient.mk (standardComplexificationIdeal R) p =
      Ideal.Quotient.mk (standardComplexificationIdeal R)
        (p %ₘ standardComplexificationPolynomial R) := by
  let q : Polynomial R := standardComplexificationPolynomial R
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := standardComplexificationIdeal R) p (p %ₘ q)).mpr
  rw [standardComplexificationIdeal,
    show standardComplexificationPolynomial R = q from rfl,
    Ideal.mem_span_singleton]
  refine ⟨p /ₘ q, ?_⟩
  dsimp [q]
  rw [Polynomial.modByMonic_eq_sub_mul_div p (standardComplexificationPolynomial R)]
  ring

theorem standardComplexification_exists_algebraMap_add_mul_I
    {R : Type u} [Field R] (z : StandardComplexification R) :
    ∃ a b : R,
      z = algebraMap R (StandardComplexification R) a +
        algebraMap R (StandardComplexification R) b * standardComplexificationI R := by
  induction z using Quotient.inductionOn' with
  | h p =>
      let q : Polynomial R := standardComplexificationPolynomial R
      let r : Polynomial R := p %ₘ q
      have hqmonic : q.Monic := by
        dsimp [q, standardComplexificationPolynomial]
        simpa using
          (Polynomial.monic_X_pow_add_C (R := R) (a := (1 : R)) (n := 2)
            (by norm_num))
      have hqne_one : q ≠ 1 := by
        dsimp [q, standardComplexificationPolynomial]
        exact Polynomial.X_pow_add_C_ne_one
          (R := R) (n := 2) (by norm_num) 1
      have hqdeg : q.natDegree = 2 := by
        dsimp [q, standardComplexificationPolynomial]
        simpa using
          (Polynomial.natDegree_X_pow_add_C (R := R) (n := 2) (r := (1 : R)))
      have hrdeg : r.natDegree < 2 := by
        calc
          r.natDegree < q.natDegree := by
            dsimp [r]
            exact Polynomial.natDegree_modByMonic_lt p hqmonic hqne_one
          _ = 2 := hqdeg
      have hlin :
          r = Polynomial.C (r.coeff 0) + Polynomial.C (r.coeff 1) * Polynomial.X :=
        Polynomial.eq_C_add_C_mul_X_of_natDegree_lt_two hrdeg
      refine ⟨r.coeff 0, r.coeff 1, ?_⟩
      calc
        Ideal.Quotient.mk (standardComplexificationIdeal R) p =
            Ideal.Quotient.mk (standardComplexificationIdeal R) r := by
              dsimp [r, q]
              exact standardComplexification_mk_eq_modByMonic p
        _ = Ideal.Quotient.mk (standardComplexificationIdeal R)
            (Polynomial.C (r.coeff 0) + Polynomial.C (r.coeff 1) * Polynomial.X) := by
              exact congrArg (Ideal.Quotient.mk (standardComplexificationIdeal R)) hlin
        _ = algebraMap R (StandardComplexification R) (r.coeff 0) +
              algebraMap R (StandardComplexification R) (r.coeff 1) *
                standardComplexificationI R := by
              change Ideal.Quotient.mk (standardComplexificationIdeal R)
                  (Polynomial.C (r.coeff 0) + Polynomial.C (r.coeff 1) * Polynomial.X) =
                Ideal.Quotient.mk (standardComplexificationIdeal R)
                    (Polynomial.C (r.coeff 0)) +
                  Ideal.Quotient.mk (standardComplexificationIdeal R)
                    (Polynomial.C (r.coeff 1)) *
                    Ideal.Quotient.mk (standardComplexificationIdeal R) Polynomial.X
              rw [map_add, map_mul]

theorem standardComplexification_square_algebraMap_add_mul_I
    {R : Type u} [Field R] (a b : R) :
    (algebraMap R (StandardComplexification R) a +
        algebraMap R (StandardComplexification R) b * standardComplexificationI R) ^ 2 =
      algebraMap R (StandardComplexification R) (a ^ 2 - b ^ 2) +
        algebraMap R (StandardComplexification R) (2 * a * b) *
          standardComplexificationI R := by
  let I : StandardComplexification R := standardComplexificationI R
  have hI : I ^ 2 = -(1 : StandardComplexification R) := by
    simpa [I] using standardComplexificationI_sq R
  change ((algebraMap R (StandardComplexification R) a) +
      (algebraMap R (StandardComplexification R) b) * I) ^ 2 =
    algebraMap R (StandardComplexification R) (a ^ 2 - b ^ 2) +
      algebraMap R (StandardComplexification R) (2 * a * b) * I
  rw [sq]
  ring_nf
  rw [hI]
  simp only [map_mul, map_sub, map_pow, map_ofNat]
  ring_nf

theorem standardComplexification_algebraMap_add_mul_I_eq_zero_iff
    {R : Type u} [Field R] (a b : R) :
    algebraMap R (StandardComplexification R) a +
        algebraMap R (StandardComplexification R) b * standardComplexificationI R = 0 ↔
      a = 0 ∧ b = 0 := by
  constructor
  · intro h
    let p : Polynomial R := Polynomial.C a + Polynomial.C b * Polynomial.X
    let q : Polynomial R := standardComplexificationPolynomial R
    have hquot : Ideal.Quotient.mk (standardComplexificationIdeal R) p = 0 := by
      dsimp [p, standardComplexificationI]
      change Ideal.Quotient.mk (standardComplexificationIdeal R)
          (Polynomial.C a + Polynomial.C b * Polynomial.X) = 0 at h
      exact h
    have hmem : p ∈ standardComplexificationIdeal R :=
      Ideal.Quotient.eq_zero_iff_mem.mp hquot
    have hdvd : q ∣ p := by
      rw [standardComplexificationIdeal,
        show standardComplexificationPolynomial R = q from rfl,
        Ideal.mem_span_singleton] at hmem
      exact hmem
    have hpdeg : p.natDegree < q.natDegree := by
      have hp : p.natDegree < 2 := by
        dsimp [p]
        compute_degree!
      have hq : q.natDegree = 2 := by
        dsimp [q, standardComplexificationPolynomial]
        simpa using
          (Polynomial.natDegree_X_pow_add_C (R := R) (n := 2) (r := (1 : R)))
      calc
        p.natDegree < 2 := hp
        _ = q.natDegree := hq.symm
    have hpzero : p = 0 := Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hpdeg
    have ha : a = 0 := by
      have hcoeff := congrArg (fun f : Polynomial R => f.coeff 0) hpzero
      simpa [p] using hcoeff
    have hb : b = 0 := by
      have hcoeff := congrArg (fun f : Polynomial R => f.coeff 1) hpzero
      simpa [p] using hcoeff
    exact ⟨ha, hb⟩
  · rintro ⟨rfl, rfl⟩
    simp

instance standardComplexification.instNontrivial
    {R : Type u} [Field R] : Nontrivial (StandardComplexification R) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hnormal :
      algebraMap R (StandardComplexification R) (1 : R) +
          algebraMap R (StandardComplexification R) (0 : R) *
            standardComplexificationI R = 0 := by
    simpa using h.symm
  have hR :=
    (standardComplexification_algebraMap_add_mul_I_eq_zero_iff
      (1 : R) (0 : R)).mp hnormal
  exact one_ne_zero hR.1

theorem standardComplexification_exists_sq_eq
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (z : StandardComplexification R) :
    ∃ w : StandardComplexification R, w ^ 2 = z := by
  rcases standardComplexification_exists_algebraMap_add_mul_I z with ⟨a, b, hz⟩
  rcases exists_imaginary_quadratic_square_coeffs
      (c := (1 : R)) (zero_lt_one : (0 : R) < 1) a b with
    ⟨u, v, hreal, himag⟩
  refine ⟨algebraMap R (StandardComplexification R) u +
      algebraMap R (StandardComplexification R) v * standardComplexificationI R, ?_⟩
  rw [standardComplexification_square_algebraMap_add_mul_I]
  rw [hz]
  have hreal' : u ^ 2 - v ^ 2 = a := by
    simpa using hreal
  rw [hreal', himag]

/-- The cubic-root exploration is preserved on the research branch. -/
theorem quadratic_monic_has_root_of_forall_sq_eq
    {K : Type u} [Field K]
    (hsqrt : ∀ z : K, ∃ w : K, w ^ 2 = z) (h2 : (2 : K) ≠ 0) (b c : K) :
    ∃ z : K,
      (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c :
        Polynomial K).eval z = 0 := by
  rcases hsqrt (b ^ 2 - 4 * c) with ⟨s, hs⟩
  refine ⟨(-b + s) / 2, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C]
  field_simp [h2]
  ring_nf
  rw [hs]
  ring

/-- A field in which every element is a square has no nontrivial quadratic
extension.  We choose an element outside the base field, use its minimal
polynomial, and then apply the quadratic root formula. -/
theorem not_quadraticExtension_of_forall_sq_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L]
    (hsqrt : ∀ z : K, ∃ w : K, w ^ 2 = z) (h2 : (2 : K) ≠ 0) : False := by
  have hfin : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  have hnot_surj : ¬ Function.Surjective (algebraMap K L) := by
    intro hsurj
    have hf : Function.Bijective (Algebra.ofId K L) := by
      constructor
      · intro x y hxy
        apply FaithfulSMul.algebraMap_injective K L
        simpa only [Algebra.ofId_apply] using hxy
      · intro y
        rcases hsurj y with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        simpa only [Algebra.ofId_apply] using hx
    have e : K ≃ₐ[K] L := AlgEquiv.ofBijective (Algebra.ofId K L) hf
    have hfin_one : Module.finrank K L = 1 := by
      rw [← e.toLinearEquiv.finrank_eq]
      simp
    omega
  have hex : ∃ α : L, α ∉ Set.range (algebraMap K L) := by
    by_contra h
    push Not at h
    exact hnot_surj h
  rcases hex with ⟨α, hα⟩
  have hαint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hminirr : Irreducible (minpoly K α) := minpoly.irreducible hαint
  have hminmonic : (minpoly K α).Monic := minpoly.monic hαint
  have hpos : 0 < (minpoly K α).natDegree := minpoly.natDegree_pos hαint
  have hne_one : (minpoly K α).natDegree ≠ 1 := by
    intro h1
    exact hα ((minpoly.natDegree_eq_one_iff).mp h1)
  have hle : (minpoly K α).natDegree ≤ 2 := by
    have hle' := minpoly.natDegree_le (A := K) (B := L) α
    rw [hfin] at hle'
    exact hle'
  have hdeg : (minpoly K α).natDegree = 2 := by omega
  rcases Polynomial.isMonicOfDegree_two_iff.mp ⟨hdeg, hminmonic⟩ with ⟨b, c, hpoly⟩
  rcases quadratic_monic_has_root_of_forall_sq_eq hsqrt h2 b c with ⟨z, hz⟩
  have hroot : (minpoly K α).IsRoot z := by
    rw [hpoly]
    simpa [Polynomial.IsRoot] using hz
  have hdegone : (minpoly K α).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (Polynomial.degree_eq_one_of_irreducible_of_root hminirr hroot)
  omega

/- The cubic and quartic irreducibility exploration is preserved on the research branch. -/

end RatFunc

end RatFuncWittLocalGlobal
