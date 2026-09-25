/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Polynomial.NonlinearIrreducible.ResidueFields

/-!
# Standard complexification and nonlinear factor consequences
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

open scoped IntermediateField

theorem standardComplexification_two_ne_zero
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    (2 : StandardComplexification R) ≠ 0 := by
  intro h
  change Ideal.Quotient.mk (standardComplexificationIdeal R)
      (Polynomial.C (2 : R)) = 0 at h
  have hzero :
      algebraMap R (StandardComplexification R) (2 : R) +
          algebraMap R (StandardComplexification R) (0 : R) *
            standardComplexificationI R = 0 := by
    change Ideal.Quotient.mk (standardComplexificationIdeal R) (Polynomial.C (2 : R)) +
        Ideal.Quotient.mk (standardComplexificationIdeal R) (Polynomial.C (0 : R)) *
          standardComplexificationI R = 0
    simpa using h
  have hcoeff :=
    (standardComplexification_algebraMap_add_mul_I_eq_zero_iff
      (2 : R) (0 : R)).mp hzero
  exact two_ne_zero hcoeff.1

/-- The standard complexification admits no further quadratic extension. -/
theorem not_quadraticExtension_standardComplexification
    {R L : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    [Field L] [Algebra (StandardComplexification R) L]
    [Algebra.IsQuadraticExtension (StandardComplexification R) L] : False := by
  have hπ : Irreducible (standardComplexificationPolynomial R) := by
    simpa [standardComplexificationPolynomial] using irreducible_X_sq_add_one (R := R)
  let _ : (standardComplexificationIdeal R).IsMaximal := by
    simpa [standardComplexificationIdeal] using PrincipalIdealRing.isMaximal_of_irreducible hπ
  let _ : Field (StandardComplexification R) :=
    Ideal.Quotient.field (standardComplexificationIdeal R)
  exact not_quadraticExtension_of_forall_sq_eq
    (K := StandardComplexification R) (L := L)
    standardComplexification_exists_sq_eq
    (standardComplexification_two_ne_zero (R := R))

/-- Every quadratic field extension of a real closed field is the standard
complexification.  The primitive element has an irreducible quadratic
minimal polynomial; its discriminant is not a square, so its negative is a
square and the corresponding normalized root squares to `-1`. -/
theorem quadraticExtension_algEquiv_standardComplexification
    {R K : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    [Field K] [Algebra R K] [Algebra.IsQuadraticExtension R K] :
    Nonempty (K ≃ₐ[R] StandardComplexification R) := by
  let q : Polynomial R := standardComplexificationPolynomial R
  have hq : Irreducible q := by
    simpa [q, standardComplexificationPolynomial] using irreducible_X_sq_add_one (R := R)
  have hqdeg : q.natDegree = 2 := by
    simpa only [q, standardComplexificationPolynomial] using
      (Polynomial.natDegree_X_pow_add_C (R := R) (n := 2) (r := (1 : R)))
  let I : Ideal (Polynomial R) := standardComplexificationIdeal R
  have hI : I.IsMaximal := by
    simpa [I, q, standardComplexificationIdeal] using
      PrincipalIdealRing.isMaximal_of_irreducible hq
  let _ : I.IsMaximal := hI
  let _ : Field (Polynomial R ⧸ I) := Ideal.Quotient.field I
  have hfin_std : Module.finrank R (Polynomial R ⧸ I) = 2 := by
    change Module.finrank R
      (Polynomial R ⧸ Ideal.span ({q} : Set (Polynomial R))) = 2
    rw [finrank_quotient_span_eq_natDegree]
    exact hqdeg
  let α : K := (Field.exists_primitive_element R K).choose
  have hprim : R⟮α⟯ = ⊤ := (Field.exists_primitive_element R K).choose_spec
  have hdeg : (minpoly R α).natDegree = 2 := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two R K]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq R α).mp hprim
  have hminirr : Irreducible (minpoly R α) :=
    minpoly.irreducible (Algebra.IsIntegral.isIntegral α)
  have hminmonic : (minpoly R α).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral α)
  rcases Polynomial.isMonicOfDegree_two_iff.mp ⟨hdeg, hminmonic⟩ with ⟨b, c, hpoly⟩
  have hroot : (minpoly R α).eval₂ (algebraMap R K) α = 0 := by
    simpa [Polynomial.aeval_def] using minpoly.aeval R α
  have hroot' : α ^ 2 + algebraMap R K b * α + algebraMap R K c = 0 := by
    rw [hpoly] at hroot
    simpa [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow] using hroot
  let D : R := b ^ 2 - 4 * c
  have hDnot : ¬ IsSquare D := by
    intro hDs
    rcases hDs with ⟨s, hs⟩
    let z : R := (-b + s) / 2
    have hz : (minpoly R α).eval z = 0 := by
      rw [hpoly]
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_mul, Polynomial.eval_C]
      dsimp [z]
      field_simp
      nlinarith [hs]
    have hdegone : (minpoly R α).natDegree = 1 :=
      Polynomial.natDegree_eq_of_degree_eq_some
        (Polynomial.degree_eq_one_of_irreducible_of_root hminirr hz)
    omega
  have hDneg : IsSquare (-D) := IsRealClosed.isSquare_neg_of_not_isSquare hDnot
  rcases hDneg with ⟨t, ht⟩
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hDnot
    refine ⟨0, ?_⟩
    have hDzero : D = 0 := by nlinarith [ht]
    simp [hDzero]
  let B : K := algebraMap R K b
  let C : K := algebraMap R K c
  let T : K := algebraMap R K t
  let γ : K := (2 * α + B) / T
  have hT0 : T ≠ 0 := by
    dsimp [T]
    intro h
    apply ht0
    exact (FaithfulSMul.algebraMap_injective R K) (by simpa using h)
  have hdisc : (algebraMap R K D) = B ^ 2 - 4 * C := by
    dsimp [D, B, C]
    simp only [map_sub, map_pow, map_mul, map_ofNat]
  have htK : T ^ 2 = -algebraMap R K D := by
    calc
      T ^ 2 = algebraMap R K (t * t) := by
        simp [T, pow_two]
      _ = algebraMap R K (-D) := by rw [ht]
      _ = -algebraMap R K D := by rw [map_neg]
  have hγ : γ ^ 2 = -(1 : K) := by
    dsimp [γ]
    field_simp [hT0]
    have hrootB : α ^ 2 + B * α + C = 0 := by simpa [B, C] using hroot'
    rw [hdisc] at htK
    calc
      (2 * α + B) ^ 2 =
          4 * (α ^ 2 + B * α + C) + (B ^ 2 - 4 * C) := by ring
      _ = B ^ 2 - 4 * C := by rw [hrootB]; ring
      _ = -(-(B ^ 2 - 4 * C)) := by ring
      _ = -T ^ 2 := by rw [← htK]
  have hqroot : q.eval₂ (algebraMap R K) γ = 0 := by
    dsimp [q, standardComplexificationPolynomial]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_C]
    simp [hγ]
  let f : (Polynomial R ⧸ I) →ₐ[R] K := by
    change AdjoinRoot q →ₐ[R] K
    exact AdjoinRoot.liftAlgHom q (Algebra.ofId R K) γ hqroot
  have hf_inj : Function.Injective f := f.toRingHom.injective
  have hfin_K : Module.finrank R K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two R K
  have hf_surj : Function.Surjective f := by
    let hmonicq : q.Monic := by
      simpa [q, standardComplexificationPolynomial] using
        (Polynomial.monic_X_pow_add_C (R := R) (a := (1 : R)) (n := 2)
          (by norm_num))
    let _ : Module.Finite R (Polynomial R ⧸ I) := by
      change Module.Finite R (AdjoinRoot q)
      exact hmonicq.finite_adjoinRoot
    have hsurj_lin : Function.Surjective f.toLinearMap :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (hfin_std.trans hfin_K.symm)).mp (by
          intro x y hxy
          exact hf_inj hxy)
    exact hsurj_lin
  exact ⟨(AlgEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm⟩

/- A finite Galois extension of a real closed field has degree at most two.
   The 2-group structure from the preceding theorem is combined with two
   successive fixed fields; if the degree were at least three, this produces
   a quadratic extension of the standard complexification, which is
   impossible because every element of that field is a square. -/
theorem finiteGalois_finrank_le_two_realClosed
    {R L : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L] :
    Module.finrank R L ≤ 2 := by
  obtain ⟨n, hcard⟩ := finiteGalois_card_is_two_power_of_realClosed (R := R) (L := L)
  have hfin_card : Module.finrank R L = 2 ^ n := by
    rw [← IsGalois.card_aut_eq_finrank R L]
    exact hcard
  by_contra hnot
  have hfin_ge : 3 ≤ Module.finrank R L := by omega
  have hn_ge : 2 ≤ n := by
    rw [hfin_card] at hfin_ge
    by_contra hn
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl <;> norm_num at hfin_ge
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let G := Gal(L / R)
  have hG : IsPGroup 2 G := IsPGroup.of_card hcard
  have hpowK : 2 ^ (n - 1) ≤ Nat.card G := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)
  obtain ⟨K, hKcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hG hpowK
  have hpowH : 2 ^ (n - 2) ≤ Nat.card K := by
    rw [hKcard]
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  obtain ⟨H, hHK, hHcard⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card Nat.prime_two hG
      (H := K) hpowH
  let E : IntermediateField R L := IntermediateField.fixedField (K : Subgroup G)
  let F : IntermediateField R L := IntermediateField.fixedField (H : Subgroup G)
  have hEFle : E ≤ F := by
    dsimp [E, F]
    exact IntermediateField.fixedField_le hHK
  let _ : Algebra E F := (IntermediateField.inclusion hEFle).toAlgebra
  have hErel : Module.finrank E L = Nat.card K := by
    exact IntermediateField.finrank_fixedField_eq_card (K : Subgroup G)
  have hFrel : Module.finrank F L = Nat.card H := by
    exact IntermediateField.finrank_fixedField_eq_card (H : Subgroup G)
  have hKindex : K.index = 2 := by
    have hidx : K.index * 2 ^ (n - 1) = 2 ^ n := by
      rw [← hKcard, K.index_mul_card, hcard]
    have hn1 : 1 ≤ n := by omega
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      calc
        2 ^ n = 2 ^ ((n - 1) + 1) := by
          exact congrArg (fun k : ℕ => 2 ^ k) (show n = (n - 1) + 1 by omega)
        _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (n - 1) := by ring
    have hidx' : K.index * 2 ^ (n - 1) = 2 * 2 ^ (n - 1) := hidx.trans hpow
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ (n - 1)) hidx'
  have hEfin : Module.finrank R E = 2 := by
    have hprod : Module.finrank R E * Nat.card K = Nat.card G := by
      calc
        Module.finrank R E * Nat.card K =
            Module.finrank R E * Module.finrank E L := by rw [hErel]
        _ = Module.finrank R L := Module.finrank_mul_finrank R E L
        _ = Nat.card G := by simpa [G] using (IsGalois.card_aut_eq_finrank R L).symm
    have hidx := K.index_mul_card
    rw [hKindex] at hidx
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card K)
    exact hprod.trans hidx.symm
  let _ : Module.Free R E := Module.Free.of_divisionRing R E
  let _ : Algebra.IsQuadraticExtension R E := ⟨hEfin⟩
  rcases quadraticExtension_algEquiv_standardComplexification (R := R) (K := E) with ⟨e⟩
  have hHcard_rel : Nat.card K = 2 * Nat.card H := by
    have hn2 : 2 ≤ n := hn_ge
    rw [hKcard, hHcard, show n - 1 = (n - 2) + 1 by omega, pow_succ]
    ring
  have hEFfin : Module.finrank E F = 2 := by
    let _ : IsScalarTower E F L := .of_algebraMap_eq (by intro x; rfl)
    have hprod : Module.finrank E F * Nat.card H = Nat.card K := by
      rw [← hFrel, ← hErel]
      exact Module.finrank_mul_finrank E F L
    have hcard' := hprod.trans hHcard_rel
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card H)
    exact hcard'
  let _ : Module.Free E F := Module.Free.of_divisionRing E F
  let _ : Algebra.IsQuadraticExtension E F := ⟨hEFfin⟩
  have hπ : Irreducible (standardComplexificationPolynomial R) := by
    simpa [standardComplexificationPolynomial] using irreducible_X_sq_add_one (R := R)
  let _ : (standardComplexificationIdeal R).IsMaximal := by
    simpa [standardComplexificationIdeal] using PrincipalIdealRing.isMaximal_of_irreducible hπ
  let _ : Field (StandardComplexification R) :=
    Ideal.Quotient.field (standardComplexificationIdeal R)
  let g : (StandardComplexification R) →+* F :=
    (IntermediateField.inclusion hEFle).toRingHom.comp e.symm.toRingHom
  let _ : Algebra (StandardComplexification R) F := g.toAlgebra
  have hfin_stdF : Module.finrank (StandardComplexification R) F = 2 := by
    have hfin_eq : Module.finrank E F = Module.finrank (StandardComplexification R) F := by
      apply Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl F)
      ext x
      simp [g, RingHom.algebraMap_toAlgebra]
    exact hfin_eq.symm.trans hEFfin
  let _ : Module.Free (StandardComplexification R) F :=
    Module.Free.of_divisionRing _ _
  let _ : Algebra.IsQuadraticExtension (StandardComplexification R) F := ⟨hfin_stdF⟩
  exact not_quadraticExtension_standardComplexification (R := R) (L := F)

/-- Every irreducible over a real closed field has degree at most two. -/
theorem irreducibleNatDegreeLeTwo_of_realClosed
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    IrreducibleNatDegreeLeTwo R := by
  intro p hp
  let L := p.SplittingField
  let _ : FiniteDimensional R L := Polynomial.IsSplittingField.finiteDimensional L p
  let _ : IsGalois R L := IsGalois.of_separable_splitting_field (p := p) hp.separable
  have hfin : Module.finrank R L ≤ 2 :=
    finiteGalois_finrank_le_two_realClosed (R := R) (L := L)
  have hdvd : p.natDegree ∣ Module.finrank R L :=
    Polynomial.Irreducible.natDegree_dvd_finrank (K := R) (L := L) hp
      (Polynomial.SplittingField.splits p)
  exact (Nat.le_of_dvd (Module.finrank_pos) hdvd).trans hfin

theorem nonlinearIrreducibleNatDegreeTwo_of_realClosed
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    NonlinearIrreducibleNatDegreeTwo R :=
  nonlinearIrreducibleNatDegreeTwo_of_irreducibleNatDegreeLeTwo
    (irreducibleNatDegreeLeTwo_of_realClosed (R := R))

/-- Alternative algebraic-closedness criteria are preserved on the research branch. -/
theorem nonlinearIrreducibleQuotientSquares_of_natDegreeTwo_of_quadraticQuotients
    {R : Type u} [Field R]
    (hdeg : NonlinearIrreducibleNatDegreeTwo R)
    (hquad : QuadraticIrreducibleQuotientSquares R) :
    NonlinearIrreducibleQuotientSquares R := by
  intro π f hπ hnonlinear
  exact hquad π f hπ (hdeg π hπ hnonlinear)

theorem nonlinearIrreducibleQuotientSquares_of_natDegreeTwo_realClosed
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hdeg : NonlinearIrreducibleNatDegreeTwo R) :
    NonlinearIrreducibleQuotientSquares R :=
  nonlinearIrreducibleQuotientSquares_of_natDegreeTwo_of_quadraticQuotients
    hdeg (quadraticIrreducibleQuotientSquares_of_realClosed R)

/-- Alternative quotient criteria are preserved on the research branch. -/
theorem nonlinearIrreducibleDivisorSquareMod_of_quotientSquares
    {R : Type u} [Field R]
    (hquot : NonlinearIrreducibleQuotientSquares R) :
    NonlinearIrreducibleDivisorSquareMod R := by
  intro π f hπ hdeg
  exact isSquareMod_of_isSquare_quotient_span_singleton (hquot π f hπ hdeg)

theorem nonlinearIrreducibleDivisorSquareMod_of_natDegreeTwo_realClosed
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hdeg : NonlinearIrreducibleNatDegreeTwo R) :
    NonlinearIrreducibleDivisorSquareMod R :=
  nonlinearIrreducibleDivisorSquareMod_of_quotientSquares
    (nonlinearIrreducibleQuotientSquares_of_natDegreeTwo_realClosed hdeg)

theorem nonlinearIrreducibleDivisorSquareMod_of_realClosed
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    NonlinearIrreducibleDivisorSquareMod R :=
  nonlinearIrreducibleDivisorSquareMod_of_natDegreeTwo_realClosed
    (nonlinearIrreducibleNatDegreeTwo_of_realClosed (R := R))

/- Alternative divisor criteria are preserved on the research branch. -/

end RatFunc

end RatFuncWittLocalGlobal
