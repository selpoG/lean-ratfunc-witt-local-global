/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Ternary.Quaternion.Polynomial.Residues

/-!
# Polynomial quaternion split criteria
-/

namespace RatFuncWittLocalGlobal

universe u v

variable {R : Type u}

/--
Polynomial-specialized finite-residue split criterion.

Unlike `PolynomialTernaryQuaternionSplitCriterion`, this version has no
infinity-place predicate.  The real-split hypothesis is supplied separately.
-/
def PolynomialTernaryQuaternionFiniteSplitCriterion [Field R] : Prop :=
  ∀ A B C : Polynomial R,
    A ≠ 0 →
      B ≠ 0 →
        C ≠ 0 →
          Squarefree A →
            Squarefree B →
              Squarefree C →
                IsCoprime A B →
                  IsCoprime A C →
                    IsCoprime B C →
                      PolynomialTernaryQuaternionFiniteResiduesTrivialFor
                        (PolynomialTernaryFiniteResidueTrivial A B C) A B C →
                        RatFuncQuaternionRealSplit.{u, u}
                          (polynomialTernaryQuaternionCoeff A B)
                          (polynomialTernaryQuaternionCoeff A C) →
                          QuaternionSymbolSplit
                            (polynomialTernaryQuaternionCoeff A B)
                            (polynomialTernaryQuaternionCoeff A C)

/--
A finite polynomial split criterion supplies the older finite/infinity
polynomial split criterion by forgetting the infinity predicate.
-/
theorem polynomialTernaryQuaternionSplitCriterion_of_finiteCriterion
    [LinearOrder R] [Field R]
    (hcriterion : PolynomialTernaryQuaternionFiniteSplitCriterion (R := R)) :
    PolynomialTernaryQuaternionSplitCriterion (R := R) := by
  intro A B C hA0 hB0 hC0 hAsq hBsq hCsq hAB hAC hBC hres hreal
  exact
    hcriterion A B C hA0 hB0 hC0 hAsq hBsq hCsq hAB hAC hBC hres.1 hreal

/--
Realization principle for the two infinity orderings.  It says that a common
strict sign detected from leading coefficients at `+∞` or `-∞` gives an actual
same-strict-sign ordering of the corresponding rational functions.
-/
def PolynomialTernaryInfinitySignRealization [LinearOrder R] [Field R] : Prop :=
  ∀ A B C : Polynomial R,
    PolynomialTernaryCommonStrictSignAtInfinity A B C →
      RatFunc.SameStrictSignOrdering
        (algebraMap (Polynomial R) (RatFunc R) A)
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C)

/-- A homomorphism realizing strict signs at `+∞`. -/
def PolynomialPosInfinitySignHomRealization
    (R : Type u) [LinearOrder R] [Field R] : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K),
    ∃ f : RatFunc R →+* K,
      (∀ P : Polynomial R, PolynomialPosAtPosInfinity P →
        0 < f (algebraMap (Polynomial R) (RatFunc R) P)) ∧
      (∀ P : Polynomial R, PolynomialNegAtPosInfinity P →
        f (algebraMap (Polynomial R) (RatFunc R) P) < 0)

/-- A homomorphism realizing strict signs at `-∞`. -/
def PolynomialNegInfinitySignHomRealization
    (R : Type u) [LinearOrder R] [Field R] : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K),
    ∃ f : RatFunc R →+* K,
      (∀ P : Polynomial R, PolynomialPosAtNegInfinity P →
        0 < f (algebraMap (Polynomial R) (RatFunc R) P)) ∧
      (∀ P : Polynomial R, PolynomialNegAtNegInfinity P →
        f (algebraMap (Polynomial R) (RatFunc R) P) < 0)

/-- The concrete Laurent-series homomorphism realizes signs at `+∞`. -/
theorem polynomialPosInfinitySignHomRealization_laurentSeries
    [LinearOrder R] [Field R] [IsStrictOrderedRing R] :
    PolynomialPosInfinitySignHomRealization R := by
  let φlaur : Polynomial R →+* LaurentSeries R :=
    Polynomial.eval₂RingHom (algebraMap R (LaurentSeries R))
      (HahnSeries.single (-1 : ℤ) (1 : R))
  let φ : Polynomial R →+* Lex (LaurentSeries R) :=
    (RatFunc.toLexRingHom (LaurentSeries R)).comp φlaur
  have hφ_apply (p : Polynomial R) : ofLex (φ p) = φlaur p := by
    rfl
  have hφ : nonZeroDivisors (Polynomial R) ≤
      (nonZeroDivisors (Lex (LaurentSeries R))).comap φ := by
    intro p hp
    rw [Submonoid.mem_comap]
    refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
    intro hzero
    have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
    have hlead :
        (ofLex (φ p)).leadingCoeff = p.leadingCoeff := by
      rw [hφ_apply]
      change
        (Polynomial.eval₂ (algebraMap R (LaurentSeries R))
            (HahnSeries.single (-1 : ℤ) (1 : R)) p).leadingCoeff =
          p.leadingCoeff
      simpa only [one_pow, mul_one] using
        RatFunc.polynomial_eval_single_neg_one_laurentSeries_leadingCoeff
          (ε := (1 : R)) one_ne_zero hp0
    have hlead_zero : (ofLex (φ p)).leadingCoeff = 0 := by
      rw [hzero]
      simp
    exact (mt Polynomial.leadingCoeff_eq_zero.1 hp0) (hlead.symm.trans hlead_zero)
  let f : RatFunc R →+* Lex (LaurentSeries R) := RatFunc.liftRingHom φ hφ
  refine ⟨Lex (LaurentSeries R), inferInstance, inferInstance, inferInstance, f, ?_, ?_⟩
  · intro P hP
    have hmap :
        f (algebraMap (Polynomial R) (RatFunc R) P) = φ P := by
      exact RatFunc.liftRingHom_algebraMap φ hφ _
    exact hmap.symm ▸ RatFunc.polynomial_posInfinity_eval_pos_laurentSeries hP
  · intro P hP
    have hmap :
        f (algebraMap (Polynomial R) (RatFunc R) P) = φ P := by
      exact RatFunc.liftRingHom_algebraMap φ hφ _
    exact hmap.symm ▸ RatFunc.polynomial_posInfinity_eval_neg_laurentSeries hP

/-- The concrete Laurent-series homomorphism realizes signs at `-∞`. -/
theorem polynomialNegInfinitySignHomRealization_laurentSeries
    [LinearOrder R] [Field R] [IsStrictOrderedRing R] :
    PolynomialNegInfinitySignHomRealization R := by
  let φlaur : Polynomial R →+* LaurentSeries R :=
    Polynomial.eval₂RingHom (algebraMap R (LaurentSeries R))
      (HahnSeries.single (-1 : ℤ) (-1 : R))
  let φ : Polynomial R →+* Lex (LaurentSeries R) :=
    (RatFunc.toLexRingHom (LaurentSeries R)).comp φlaur
  have hφ_apply (p : Polynomial R) : ofLex (φ p) = φlaur p := by
    rfl
  have hφ : nonZeroDivisors (Polynomial R) ≤
      (nonZeroDivisors (Lex (LaurentSeries R))).comap φ := by
    intro p hp
    rw [Submonoid.mem_comap]
    refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
    intro hzero
    have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
    have hlead :
        (ofLex (φ p)).leadingCoeff = p.leadingCoeff * (-1 : R) ^ p.natDegree := by
      rw [hφ_apply]
      change
        (Polynomial.eval₂ (algebraMap R (LaurentSeries R))
            (HahnSeries.single (-1 : ℤ) (-1 : R)) p).leadingCoeff =
          p.leadingCoeff * (-1 : R) ^ p.natDegree
      exact RatFunc.polynomial_eval_single_neg_one_laurentSeries_leadingCoeff
        (ε := (-1 : R)) (neg_ne_zero.mpr one_ne_zero) hp0
    have hlead_zero : (ofLex (φ p)).leadingCoeff = 0 := by
      rw [hzero]
      simp
    have hlc_ne : p.leadingCoeff ≠ 0 :=
      mt Polynomial.leadingCoeff_eq_zero.1 hp0
    have hpow_ne : (-1 : R) ^ p.natDegree ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    exact mul_ne_zero hlc_ne hpow_ne (hlead.symm.trans hlead_zero)
  let f : RatFunc R →+* Lex (LaurentSeries R) := RatFunc.liftRingHom φ hφ
  refine ⟨Lex (LaurentSeries R), inferInstance, inferInstance, inferInstance, f, ?_, ?_⟩
  · intro P hP
    have hmap :
        f (algebraMap (Polynomial R) (RatFunc R) P) = φ P := by
      exact RatFunc.liftRingHom_algebraMap φ hφ _
    exact hmap.symm ▸ RatFunc.polynomial_negInfinity_eval_pos_laurentSeries hP
  · intro P hP
    have hmap :
        f (algebraMap (Polynomial R) (RatFunc R) P) = φ P := by
      exact RatFunc.liftRingHom_algebraMap φ hφ _
    exact hmap.symm ▸ RatFunc.polynomial_negInfinity_eval_neg_laurentSeries hP

/--
Hom-realization of both infinity orderings implies the ordering-level infinity
sign realization.
-/
theorem polynomialTernaryInfinitySignRealization_of_hom
    [LinearOrder R] [Field R]
    (hposInf : PolynomialPosInfinitySignHomRealization R)
    (hnegInf : PolynomialNegInfinitySignHomRealization R) :
    PolynomialTernaryInfinitySignRealization (R := R) := by
  intro A B C hcommon
  rcases hposInf with ⟨Kp, hKpField, hKpOrder, hKpStrict, fp, hp_pos, hp_neg⟩
  rcases hnegInf with ⟨Kn, hKnField, hKnOrder, hKnStrict, fn, hn_pos, hn_neg⟩
  rcases hcommon with hposCommon | hnegCommon
  · rcases hposCommon with hpos | hneg
    · let _ : Field Kp := hKpField
      let _ : LinearOrder Kp := hKpOrder
      let _ : IsStrictOrderedRing Kp := hKpStrict
      exact RatFunc.sameStrictSignOrdering_of_hom_pos fp
        (hp_pos A hpos.1) (hp_pos B hpos.2.1) (hp_pos C hpos.2.2)
    · let _ : Field Kp := hKpField
      let _ : LinearOrder Kp := hKpOrder
      let _ : IsStrictOrderedRing Kp := hKpStrict
      exact RatFunc.sameStrictSignOrdering_of_hom_neg fp
        (hp_neg A hneg.1) (hp_neg B hneg.2.1) (hp_neg C hneg.2.2)
  · rcases hnegCommon with hpos | hneg
    · let _ : Field Kn := hKnField
      let _ : LinearOrder Kn := hKnOrder
      let _ : IsStrictOrderedRing Kn := hKnStrict
      exact RatFunc.sameStrictSignOrdering_of_hom_pos fn
        (hn_pos A hpos.1) (hn_pos B hpos.2.1) (hn_pos C hpos.2.2)
    · let _ : Field Kn := hKnField
      let _ : LinearOrder Kn := hKnOrder
      let _ : IsStrictOrderedRing Kn := hKnStrict
      exact RatFunc.sameStrictSignOrdering_of_hom_neg fn
        (hn_neg A hneg.1) (hn_neg B hneg.2.1) (hn_neg C hneg.2.2)

/-- The two infinity orderings of `RatFunc R` are realized by Laurent-series homomorphisms. -/
theorem polynomialTernaryInfinitySignRealization_laurentSeries
    [LinearOrder R] [Field R] [IsStrictOrderedRing R] :
    PolynomialTernaryInfinitySignRealization (R := R) :=
  polynomialTernaryInfinitySignRealization_of_hom
    polynomialPosInfinitySignHomRealization_laurentSeries
    polynomialNegInfinitySignHomRealization_laurentSeries

/--
If common strict signs at infinity can be realized as orderings of `RatFunc R`,
then absence of a same-strict-sign ordering supplies the no-common-sign
condition at infinity.
-/
theorem polynomialTernaryNoCommonStrictSignAtInfinity_of_not_sameStrictSign
    [LinearOrder R] [Field R]
    (hinftyRealization : PolynomialTernaryInfinitySignRealization (R := R))
    {A B C : Polynomial R}
    (hno :
      ¬ RatFunc.SameStrictSignOrdering
        (algebraMap (Polynomial R) (RatFunc R) A)
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C)) :
    PolynomialTernaryNoCommonStrictSignAtInfinity A B C
      (polynomialTernaryQuaternionCoeff A B)
      (polynomialTernaryQuaternionCoeff A C) := by
  intro hcommon
  exact hno (hinftyRealization A B C hcommon)

/--
The existing polynomial Legendre local conditions provide the finite-place
residue component for the normalized quaternion symbol.
-/
theorem polynomialTernaryFiniteResidueTrivial_of_legendreLocalConditions
    [Field R] {A B C : Polynomial R}
    (hlocal : RatFunc.PolynomialLegendreLocalConditions A B C) :
    ∀ π : Polynomial R, Irreducible π →
      PolynomialTernaryFiniteResidueTrivial A B C
        (polynomialTernaryQuaternionCoeff A B)
        (polynomialTernaryQuaternionCoeff A C) π := by
  intro π hπ
  rcases hlocal with ⟨hA, hB, hC⟩
  exact ⟨hA π hπ, hB π hπ, hC π hπ⟩

/--
The existing Legendre finite local conditions also provide the finite
tame-residue condition for the normalized quaternion symbol.
-/
theorem polynomialTernaryFiniteTameResidueTrivial_of_legendreLocalConditions
    [Field R] {A B C : Polynomial R}
    (hlocal : RatFunc.PolynomialLegendreLocalConditions A B C) :
    ∀ π : Polynomial R, Irreducible π →
      PolynomialTernaryFiniteTameResidueTrivial A B C
        (polynomialTernaryQuaternionCoeff A B)
        (polynomialTernaryQuaternionCoeff A C) π := by
  intro π hπ
  exact
    polynomialTernaryFiniteTameResidueTrivial_of_component
      (polynomialTernaryFiniteResidueTrivial_of_legendreLocalConditions
        hlocal π hπ)

/--
The existing Legendre finite local conditions provide the finite tame-residue
input for the normalized polynomial quaternion symbol.
-/
theorem polynomialTernaryQuaternionFiniteTameResiduesTrivialFor_of_legendreLocalConditions
    [Field R] {A B C : Polynomial R}
    (hlocal : RatFunc.PolynomialLegendreLocalConditions A B C) :
    PolynomialTernaryQuaternionFiniteResiduesTrivialFor
      (PolynomialTernaryFiniteTameResidueTrivial A B C) A B C :=
  polynomialTernaryFiniteTameResidueTrivial_of_legendreLocalConditions hlocal

/-!
For an arbitrary nonzero right coefficient, first remove its square part
`C = Cₛ * c²`.  The resolver is then applied to the squarefree pair
`(A*B,A*Cₛ)`.  The successor WholeMod and finite packages are rebuilt from
the returned local conditions, while the square-factor transport restores the
original cleared and real split predicates.
-/

theorem polynomialTernaryClearedQuaternionSplit_gcdSplit_normalization_of_arbitrary_right
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hAsq : Squarefree A) (hBsq : Squarefree B)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C)
    (hreal :
      RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C)
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, v} R) :
    RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ∨
      ∃ Cs c : Polynomial R,
        Cs ≠ 0 ∧ c ≠ 0 ∧ Squarefree Cs ∧ C = Cs * c ^ 2 ∧
          ∃ s : SquarefreeGcdSplit (A * B) (A * Cs),
            RatFunc.PolynomialLegendreLocalConditions s.G s.C₁ s.B₁ ∧
              Squarefree s.C₁ ∧ Squarefree s.B₁ ∧ Squarefree s.G ∧
                A ∣ s.G ∧ IsCoprime s.C₁ s.B₁ ∧ IsCoprime s.C₁ s.G ∧
                  IsCoprime s.B₁ s.G ∧
                    RatFunc.PolynomialLegendreWholeModConditions s.C₁ s.B₁ s.G ∧
                      PolynomialTernaryQuaternionFiniteResiduesTrivialFor
                        (PolynomialTernaryFiniteTameResidueTrivial s.C₁ s.B₁ s.G)
                        s.C₁ s.B₁ s.G ∧
                        (RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
                          RatFunc.PolynomialTernaryClearedQuaternionSplit s.C₁ s.B₁ s.G) ∧
                          (RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
                            RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
                              s.C₁ s.B₁ s.G) ∧
                            s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree ≤
                                A.natDegree + B.natDegree + C.natDegree ∧
                              ((¬ IsUnit c ∨ s.G.natDegree > A.natDegree) →
                                s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree <
                                  A.natDegree + B.natDegree + C.natDegree) := by
  rcases exists_squarefree_mul_square_of_ne_zero hC0 with
    ⟨Cs, c, hCs0, hc0, hCssq, hC⟩
  have hCsC : Cs ∣ C := by
    rw [hC]
    exact ⟨c ^ 2, by ring⟩
  have hACs : IsCoprime A Cs := hAC.of_isCoprime_of_dvd_right hCsC
  have hsplitTransport :
      RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
        RatFunc.PolynomialTernaryClearedQuaternionSplit A B Cs := by
    simpa using
      (RatFunc.polynomialTernaryClearedQuaternionSplit_square_factor_transport
        (A := A) (B := B) (C := C) (A' := A) (B' := B) (C' := Cs)
        (a := 1) (b := 1) (c := c)
        one_ne_zero one_ne_zero hc0 (by simp) (by simp) hC)
  have hrealTransport :
      RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B Cs := by
    simpa using
      (RatFunc.polynomialTernaryClearedQuaternionRealSplit_square_factor_transport
        (A := A) (B := B) (C := C) (A' := A) (B' := B) (C' := Cs)
        (a := 1) (b := 1) (c := c)
        one_ne_zero one_ne_zero hc0 (by simp) (by simp) hC)
  have hrealCs :
      RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B Cs :=
    hrealTransport.mp hreal
  rcases polynomialTernaryClearedQuaternionSplit_unit_first_gcdSplit_normalization_core
      hA0 hB0 hCs0 hAsq hBsq hCssq hAB hACs hrealCs hrealization with hsplit | hsucc
  · exact Or.inl (hsplitTransport.mpr hsplit)
  · rcases hsucc with ⟨s, hlocal, hC₁sq, hB₁sq, hGsq, hAG, hC₁B₁, hC₁G, hB₁G,
      hsplitCore, hrealCore, hmeasureCore, hstrictCore⟩
    have hlocalNew : RatFunc.PolynomialLegendreLocalConditions s.C₁ s.B₁ s.G := by
      refine ⟨?_, ?_, ?_⟩
      · intro π hπ hπC₁
        simpa [mul_comm] using (hlocal.2.1 π hπ hπC₁)
      · intro π hπ hπB₁
        simpa [mul_comm] using (hlocal.2.2 π hπ hπB₁)
      · intro π hπ hπG
        simpa [mul_comm] using (hlocal.1 π hπ hπG)
    have hwholeNew :=
      RatFunc.polynomialLegendreWholeModConditions_of_localConditions
        s.C₁_ne_zero s.B₁_ne_zero s.G_ne_zero
        hC₁sq hB₁sq hGsq hlocalNew
    have hfiniteNew :=
      polynomialTernaryQuaternionFiniteTameResiduesTrivialFor_of_legendreLocalConditions
        hlocalNew
    have hsplitNew :
        RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
          RatFunc.PolynomialTernaryClearedQuaternionSplit s.C₁ s.B₁ s.G :=
      hsplitTransport.trans hsplitCore
    have hrealNew :
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
          RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
            s.C₁ s.B₁ s.G :=
      hrealTransport.trans hrealCore
    have hCdeg : C.natDegree = Cs.natDegree + 2 * c.natDegree := by
      rw [hC, Polynomial.natDegree_mul hCs0 (pow_ne_zero 2 hc0),
        Polynomial.natDegree_pow]
    have hmeasure :
        s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree ≤
          A.natDegree + B.natDegree + C.natDegree := by
      omega
    have hAdegG : A.natDegree ≤ s.G.natDegree :=
      Polynomial.natDegree_le_of_dvd hAG s.G_ne_zero
    have hcpos_of_nonunit : ¬ IsUnit c → 0 < c.natDegree := by
      intro hcnu
      have hcdeg0 : c.natDegree ≠ 0 := by
        intro hcdeg
        rcases Polynomial.natDegree_eq_zero.mp hcdeg with ⟨a, ha⟩
        apply hcnu
        rw [← ha]
        apply Polynomial.isUnit_C.mpr
        apply isUnit_iff_ne_zero.mpr
        intro ha0
        apply hc0
        simpa [ha0] using ha.symm
      exact Nat.pos_of_ne_zero hcdeg0
    have hstrict :
        (¬ IsUnit c ∨ s.G.natDegree > A.natDegree) →
          s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree <
            A.natDegree + B.natDegree + C.natDegree := by
      intro hbad
      rcases hstrictCore with hGeq | hLt
      · rcases hbad with hcnu | hGgt
        · have hcpos : 0 < c.natDegree := hcpos_of_nonunit hcnu
          omega
        · omega
      · omega
    exact Or.inr ⟨Cs, c, hCs0, hc0, hCssq, hC, s, hlocal, hC₁sq, hB₁sq,
      hGsq, hAG, hC₁B₁, hC₁G, hB₁G, hwholeNew, hfiniteNew, hsplitNew,
      hrealNew, hmeasure, hstrict⟩

/-!
Compose the weighted square-part/gcd step with the arbitrary-right
normalizer.  The weighted successor has squarefree first two coefficients
`(B₁,g*C)` once the original `B,C` are squarefree and coprime; its potentially
non-squarefree right coefficient `d₁` is exactly the input handled by the
arbitrary-right endpoint.  The weighted strict measure and the normalizer's
nonincrease combine into the final strict decrease.
-/

theorem
    polynomialTernaryClearedQuaternionSplit_square_part_gcd_normalization_right
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {A B C d x : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0) (hd0 : d ≠ 0)
    (hAsq : Squarefree A) (hBsq : Squarefree B) (hCsq : Squarefree C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hBC : IsCoprime B C)
    (hwhole : RatFunc.PolynomialLegendreWholeModConditions A B C)
    (hreal : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C)
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, v} R)
    (hxd : x ^ 2 + B * C = A * d) :
    RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ∨
      ∃ g q x₀ B₀ d₀ x₁ B₁ d₁ : Polynomial R,
        g ≠ 0 ∧ q ≠ 0 ∧ Squarefree g ∧
          B = q ^ 2 * B₀ ∧ d = q ^ 2 * d₀ ∧ x = q * x₀ ∧
            x₀ ^ 2 + B₀ * C = A * d₀ ∧
              B₀ = g * B₁ ∧ d₀ = g * d₁ ∧
                g * x₁ ^ 2 + B₁ * C = A * d₁ ∧
                  IsCoprime B₁ d₁ ∧ IsCoprime B₁ (g * C) ∧
                    ∃ Cs c : Polynomial R,
                      Cs ≠ 0 ∧ c ≠ 0 ∧ Squarefree Cs ∧ d₁ = Cs * c ^ 2 ∧
                        ∃ s : SquarefreeGcdSplit (B₁ * (g * C)) (B₁ * Cs),
                          RatFunc.PolynomialLegendreLocalConditions s.G s.C₁ s.B₁ ∧
                            Squarefree s.C₁ ∧ Squarefree s.B₁ ∧ Squarefree s.G ∧
                              B₁ ∣ s.G ∧ IsCoprime s.C₁ s.B₁ ∧
                                IsCoprime s.C₁ s.G ∧ IsCoprime s.B₁ s.G ∧
                                  RatFunc.PolynomialLegendreWholeModConditions
                                    s.C₁ s.B₁ s.G ∧
                                    PolynomialTernaryQuaternionFiniteResiduesTrivialFor
                                      (PolynomialTernaryFiniteTameResidueTrivial
                                        s.C₁ s.B₁ s.G) s.C₁ s.B₁ s.G ∧
                                      (RatFunc.PolynomialTernaryClearedQuaternionSplit
                                        A B C ↔
                                        RatFunc.PolynomialTernaryClearedQuaternionSplit
                                          s.C₁ s.B₁ s.G) ∧
                                        (RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
                                          A B C ↔
                                          RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
                                            s.C₁ s.B₁ s.G) ∧
                                          s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree ≤
                                              B.natDegree + C.natDegree + d.natDegree ∧
                                            (¬ IsUnit (g * q ^ 2) →
                                              s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree <
                                                B.natDegree + C.natDegree + d.natDegree) := by
  have _hAsq := hAsq
  rcases RatFunc.polynomialTernaryClearedQuaternion_square_part_gcd_normalization
      (A := A) (B := B) (C := C) (d := d) (x := x)
      hA0 hB0 hC0 hd0 hAB hAC hBC hwhole hxd with
    ⟨g, q, x₀, B₀, d₀, x₁, B₁, d₁, hg0, hq0, hgsq, hBfac, hdfac, hx,
      hidentity, hB₀fac, hd₀fac, hweighted, hB₁d₁, _hwholeW, hsplitW, hrealW,
      hmeasureW, hstrictW⟩
  have hB₀0 : B₀ ≠ 0 := by
    intro hzero
    apply hB0
    rw [hBfac, hzero]
    simp
  have hd₀0 : d₀ ≠ 0 := by
    intro hzero
    apply hd0
    rw [hdfac, hzero]
    simp
  have hB₁0 : B₁ ≠ 0 := by
    intro hzero
    apply hB₀0
    rw [hB₀fac, hzero]
    simp
  have hd₁0 : d₁ ≠ 0 := by
    intro hzero
    apply hd₀0
    rw [hd₀fac, hzero]
    simp
  have hgB : g ∣ B := by
    refine ⟨q ^ 2 * B₁, ?_⟩
    rw [hBfac, hB₀fac]
    ring
  have hB₁dvdB : B₁ ∣ B := by
    refine ⟨q ^ 2 * g, ?_⟩
    rw [hBfac, hB₀fac]
    ring
  have hB₀sq : Squarefree B₀ := by
    apply hBsq.squarefree_of_dvd
    refine ⟨q ^ 2, ?_⟩
    rw [hBfac]
    ring
  have hGmulSq : Squarefree (g * B₁) := by
    simpa [hB₀fac] using hB₀sq
  have hB₁dvdB₀ : B₁ ∣ B₀ := by
    refine ⟨g, ?_⟩
    simpa [mul_comm] using hB₀fac
  have hB₁sq : Squarefree B₁ := hB₀sq.squarefree_of_dvd hB₁dvdB₀
  have hGrel : IsRelPrime g B₁ := IsRelPrime.of_squarefree_mul hGmulSq
  have hB₁g : IsCoprime B₁ g := hGrel.isCoprime.symm
  have hB₁C : IsCoprime B₁ C := hBC.of_isCoprime_of_dvd_left hB₁dvdB
  have hB₁gC : IsCoprime B₁ (g * C) :=
    IsCoprime.mul_right hB₁g hB₁C
  have hgC : IsCoprime g C := hBC.of_isCoprime_of_dvd_left hgB
  have hGCsq : Squarefree (g * C) := by
    exact squarefree_mul_iff.mpr ⟨hgC.isRelPrime, hgsq, hCsq⟩
  have hgC0 : g * C ≠ 0 := mul_ne_zero hg0 hC0
  have hrealW' :
      RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
        B₁ (g * C) d₁ :=
    hrealW.mp hreal
  rcases polynomialTernaryClearedQuaternionSplit_gcdSplit_normalization_of_arbitrary_right
      (A := B₁) (B := g * C) (C := d₁)
      hB₁0 hgC0 hd₁0 hB₁sq hGCsq hB₁gC hB₁d₁ hrealW' hrealization with
    hsplitN | hsuccN
  · exact Or.inl (hsplitW.mpr hsplitN)
  · rcases hsuccN with
      ⟨Cs, c, hCs0, hc0, hCssq, hd₁fac, s, hlocal, hC₁sq, hB₁sq, hGsq,
        hB₁divG, hC₁B₁, hC₁G, hB₁G, hwholeN, hfiniteN, hsplitN, hrealN,
        hmeasureN, _hstrictN⟩
    have hsplitFinal :
        RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
          RatFunc.PolynomialTernaryClearedQuaternionSplit s.C₁ s.B₁ s.G :=
      hsplitW.trans hsplitN
    have hrealFinal :
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
          RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
            s.C₁ s.B₁ s.G :=
      hrealW.trans hrealN
    have hmeasureFinal :
        s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree ≤
          B.natDegree + C.natDegree + d.natDegree := by
      omega
    have hstrictFinal :
        ¬ IsUnit (g * q ^ 2) →
          s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree <
            B.natDegree + C.natDegree + d.natDegree := by
      intro hnonunit
      have hweightedStrict := hstrictW hnonunit
      omega
    exact Or.inr ⟨g, q, x₀, B₀, d₀, x₁, B₁, d₁, hg0, hq0, hgsq, hBfac,
      hdfac, hx, hidentity, hB₀fac, hd₀fac, hweighted, hB₁d₁, hB₁gC,
      Cs, c, hCs0, hc0, hCssq, hd₁fac, s, hlocal, hC₁sq, hB₁sq, hGsq,
      hB₁divG, hC₁B₁, hC₁G, hB₁G, hwholeN, hfiniteN, hsplitFinal, hrealFinal,
      hmeasureFinal, hstrictFinal⟩

/-!
The high-level recursive step first produces the reduced quotient `d`.  The
zero quotient is terminal (the old symbol splits); in the nonzero branch the
composed weighted/arbitrary-right endpoint supplies a pairwise-squarefree
successor.  Since its measure is at most `deg B + deg C + deg d` and
`deg d < deg A`, the final decrease is unconditional.
-/

theorem
    polynomialTernaryClearedQuaternionSplit_descent_wholeMod_normalized_right
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hAdeg : 0 < A.natDegree)
    (hBCdeg : B.natDegree + C.natDegree < 2 * A.natDegree)
    (hwhole : RatFunc.PolynomialLegendreWholeModConditions A B C)
    (hAsq : Squarefree A) (hBsq : Squarefree B) (hCsq : Squarefree C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hBC : IsCoprime B C)
    (hreal : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C)
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, v} R) :
    RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ∨
      ∃ d D E : Polynomial R, ∃ s : SquarefreeGcdSplit D E,
        d ≠ 0 ∧ d.natDegree < A.natDegree ∧
          RatFunc.PolynomialLegendreLocalConditions s.G s.C₁ s.B₁ ∧
          Squarefree s.C₁ ∧ Squarefree s.B₁ ∧ Squarefree s.G ∧
            IsCoprime s.C₁ s.B₁ ∧ IsCoprime s.C₁ s.G ∧
              IsCoprime s.B₁ s.G ∧
                RatFunc.PolynomialLegendreWholeModConditions s.C₁ s.B₁ s.G ∧
                  PolynomialTernaryQuaternionFiniteResiduesTrivialFor
                    (PolynomialTernaryFiniteTameResidueTrivial s.C₁ s.B₁ s.G)
                    s.C₁ s.B₁ s.G ∧
                    (RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
                      RatFunc.PolynomialTernaryClearedQuaternionSplit s.C₁ s.B₁ s.G) ∧
                      (RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
                        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
                          s.C₁ s.B₁ s.G) ∧
                        s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree ≤
                            B.natDegree + C.natDegree + d.natDegree ∧
                          s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree <
                            A.natDegree + B.natDegree + C.natDegree := by
  rcases RatFunc.polynomialTernaryClearedQuaternionSplit_descent_with_wholeMod
      hA0 hB0 hAdeg hBCdeg hwhole hAB hAC with
    ⟨x, d, hx, hxd, hdrop, hsplitD, _hwholeD⟩
  by_cases hd0 : d = 0
  · left
    apply hsplitD.mpr
    rw [hd0]
    exact quaternionSymbolSplit_of_right_eq_zero (by simp)
  · have hddeg : d.natDegree < A.natDegree := hdrop.resolve_left hd0
    rcases
        polynomialTernaryClearedQuaternionSplit_square_part_gcd_normalization_right
        (A := A) (B := B) (C := C) (d := d) (x := x)
        hA0 hB0 hC0 hd0 hAsq hBsq hCsq hAB hAC hBC hwhole hreal hrealization hxd with
      hsplit | hsucc
    · exact Or.inl hsplit
    · rcases hsucc with
        ⟨g, q, x₀, B₀, d₀, x₁, B₁, d₁, hg0, hq0, hgsq, hBfac, hdfac, hx₀,
          hidentity, hB₀fac, hd₀fac, hweighted, hB₁d₁, hB₁gC, Cs, c, hCs0,
          hc0, hCssq, hd₁fac, s, hlocal, hC₁sq, hB₁sq, hGsq, _hB₁G,
          hC₁B₁, hC₁G, hB₁G, hwholeN, hfiniteN, hsplitN, hrealN, hmeasureN,
          _hstrictN⟩
      have hmeasureFinal :
          s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree ≤
            B.natDegree + C.natDegree + d.natDegree := by
        exact hmeasureN
      have hstrictFinal :
          s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree <
            A.natDegree + B.natDegree + C.natDegree := by
        omega
      refine Or.inr ⟨d, B₁ * (g * C), B₁ * Cs, s, hd0, hddeg, hlocal,
        hC₁sq, hB₁sq, hGsq,
        hC₁B₁, hC₁G, hB₁G, hwholeN, hfiniteN, hsplitN, hrealN,
        hmeasureFinal, hstrictFinal⟩

/-!
The recursive endpoint needs a strict inequality with one coefficient in the
pivot position.  A maximal degree supplies it unless all three degrees are
equal.  Keeping this elementary alternative explicit prevents the equal-degree
case from being hidden in a false strict-premise assumption.
-/

theorem polynomialTernaryClearedQuaternionSplit_pivot_degree_choice
    [Field R] {A B C : Polynomial R}
    (hnonconstant : 0 < A.natDegree ∨ 0 < B.natDegree ∨ 0 < C.natDegree) :
    (A.natDegree = B.natDegree ∧ B.natDegree = C.natDegree ∧
        0 < A.natDegree) ∨
      ∃ Ap Bp Cp : Polynomial R,
        ((Ap = A ∧ Bp = B ∧ Cp = C) ∨
          (Ap = B ∧ Bp = C ∧ Cp = A) ∨
            (Ap = C ∧ Bp = A ∧ Cp = B)) ∧
          0 < Ap.natDegree ∧
            Bp.natDegree + Cp.natDegree < 2 * Ap.natDegree := by
  by_cases hAB : A.natDegree = B.natDegree
  · by_cases hBC : B.natDegree = C.natDegree
    · left
      refine ⟨hAB, hBC, ?_⟩
      rcases hnonconstant with hA | hB | hC <;> omega
    · right
      by_cases hCB : C.natDegree < B.natDegree
      · refine ⟨A, B, C, Or.inl ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
        · omega
        · omega
      · have hBC' : B.natDegree < C.natDegree := by omega
        refine ⟨C, A, B, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), ?_, ?_⟩
        · omega
        · omega
  · right
    by_cases hBA : B.natDegree < A.natDegree
    · by_cases hCA : C.natDegree ≤ A.natDegree
      · refine ⟨A, B, C, Or.inl ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
        · omega
        · omega
      · have hAC : A.natDegree < C.natDegree := by omega
        refine ⟨C, A, B, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), ?_, ?_⟩
        · omega
        · omega
    · have hAB' : A.natDegree < B.natDegree := by omega
      by_cases hCB : C.natDegree ≤ B.natDegree
      · refine ⟨B, C, A, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), ?_, ?_⟩
        · omega
        · omega
      · have hBC' : B.natDegree < C.natDegree := by omega
        refine ⟨C, A, B, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), ?_, ?_⟩
        · omega
        · omega

/-!
In the equal positive-degree branch, a reduced square-modulus representative has
degree below the pivot and therefore cannot cancel the top term of `B * C`.
When the two non-pivot leading coefficients have opposite signs, real
closedness supplies a scalar square root for that top term.  Adding a suitable
constant multiple of `A` to the reduced representative preserves the square
congruence while cancelling its degree-`2 * deg A` coefficient.  The resulting
quotient is either zero or has strictly smaller degree than the pivot.
-/

theorem polynomialTernaryClearedQuaternionSplit_equal_degree_top_cancelled_witness
    [LinearOrder R] [Field R] [IsStrictOrderedRing R] [IsRealClosed R]
    {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (heqAB : A.natDegree = B.natDegree)
    (heqBC : B.natDegree = C.natDegree)
    (hAdeg : 0 < A.natDegree)
    (hneg : B.leadingCoeff * C.leadingCoeff < 0)
    (hwhole : RatFunc.PolynomialLegendreWholeModConditions A B C) :
    ∃ x d : Polynomial R,
      x ^ 2 + B * C = A * d ∧ (d = 0 ∨ d.natDegree < A.natDegree) := by
  have hBdeg : B.natDegree = A.natDegree := heqAB.symm
  have hCdeg : C.natDegree = A.natDegree := heqBC.symm.trans heqAB.symm
  have hA0lc : A.leadingCoeff ≠ 0 := by
    exact Polynomial.leadingCoeff_ne_zero.mpr hA0
  have hposBC : 0 < -(B.leadingCoeff * C.leadingCoeff) := by
    linarith
  have hsquare : IsSquare (-(B.leadingCoeff * C.leadingCoeff)) := by
    rcases IsRealClosed.isSquare_or_isSquare_neg (-(B.leadingCoeff * C.leadingCoeff)) with h | h
    · exact h
    · rcases h with ⟨r, hr⟩
      exfalso
      have hnonneg : 0 ≤ r ^ 2 := sq_nonneg r
      have hr' : B.leadingCoeff * C.leadingCoeff = r ^ 2 := by
        simpa [pow_two] using hr
      nlinarith [hneg, hr', hnonneg]
  rcases hsquare with ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    intro hrzero
    have hval : -(B.leadingCoeff * C.leadingCoeff) ≠ 0 := ne_of_gt hposBC
    apply hval
    rw [hr, hrzero]
    simp
  let t : R := r / A.leadingCoeff
  have ht0 : t ≠ 0 := div_ne_zero hr0 hA0lc
  let xr : Polynomial.degreeLT R A.natDegree :=
    RatFunc.modByNonzeroDegreeLTLinearMap A hA0 (hwhole.1.choose)
  have hxrdiv : A ∣ (xr : Polynomial R) ^ 2 + B * C := by
    apply RatFunc.dvd_square_add_of_modByNonzeroDegreeLTLinearMap hA0
    simpa [sub_eq_add_neg] using hwhole.1.choose_spec
  rcases hxrdiv with ⟨d₀, hd₀⟩
  let x : Polynomial R := (xr : Polynomial R) + A * Polynomial.C t
  have hAtdeg : (A * Polynomial.C t).natDegree = A.natDegree := by
    rw [Polynomial.natDegree_mul hA0 (Polynomial.C_ne_zero.mpr ht0),
      Polynomial.natDegree_C, Nat.add_zero]
  have hxrdeg_lt : (xr : Polynomial R).natDegree < A.natDegree := by
    by_cases hxr0 : (xr : Polynomial R) = 0
    · simp [hxr0, hAdeg]
    · exact RatFunc.polynomial_natDegree_lt_of_mem_degreeLT xr.2 hxr0
  have hxdeg : x.natDegree = A.natDegree := by
    dsimp [x]
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt]
    · exact hAtdeg
    · simpa [hAtdeg] using hxrdeg_lt
  have hxlc : x.leadingCoeff = r := by
    have hdeg_lt : (xr : Polynomial R).degree < (A * Polynomial.C t).degree := by
      exact Polynomial.degree_lt_degree (by simpa [hAtdeg] using hxrdeg_lt)
    have hadd := Polynomial.leadingCoeff_add_of_degree_lt (p := (xr : Polynomial R))
      (q := A * Polynomial.C t) hdeg_lt
    rw [hadd, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    dsimp [t]
    field_simp
  have hxd : x ^ 2 + B * C = A * (d₀ + 2 * (xr : Polynomial R) * Polynomial.C t
      + A * (Polynomial.C t) ^ 2) := by
    dsimp [x]
    simpa [add_comm, add_left_comm, add_assoc] using
      (RatFunc.squareModWitness_add_mul_quotient (A := A) (B := B) (C := C)
        (x := (xr : Polynomial R)) (d := d₀) (t := Polynomial.C t) hd₀)
  let d : Polynomial R := d₀ + 2 * (xr : Polynomial R) * Polynomial.C t
      + A * (Polynomial.C t) ^ 2
  have hxd' : x ^ 2 + B * C = A * d := by simpa [d] using hxd
  have hsumdeg : (x ^ 2 + B * C).natDegree < 2 * A.natDegree := by
    have hx2deg : (x ^ 2).natDegree = 2 * A.natDegree := by
      rw [Polynomial.natDegree_pow, hxdeg]
    have hBCdeg : (B * C).natDegree = 2 * A.natDegree := by
      rw [Polynomial.natDegree_mul hB0 hC0, hBdeg, hCdeg]
      omega
    have hle : (x ^ 2 + B * C).natDegree ≤ 2 * A.natDegree := by
      calc
        (x ^ 2 + B * C).natDegree ≤ max (x ^ 2).natDegree (B * C).natDegree :=
          Polynomial.natDegree_add_le _ _
        _ = 2 * A.natDegree := by rw [hx2deg, hBCdeg, max_self]
    have hcoeff : (x ^ 2 + B * C).coeff (2 * A.natDegree) = 0 := by
      have hBCtop : B.natDegree + C.natDegree = 2 * A.natDegree := by
        rw [hBdeg, hCdeg]
        omega
      have hcoeff' := RatFunc.polynomial_coeff_sq_add_mul_of_top_degrees
        (u := x) (B := B) (C := C)
        (k := 2 * A.natDegree) (by rw [hxdeg]) hBCtop
      rw [hcoeff', hxlc]
      have hr' : r ^ 2 = -(B.leadingCoeff * C.leadingCoeff) := by
        simpa [pow_two] using hr.symm
      rw [hr']
      ring
    by_cases hsum0 : x ^ 2 + B * C = 0
    · rw [hsum0]
      simp only [Polynomial.natDegree_zero]
      exact Nat.mul_pos (by decide) hAdeg
    have hne : (x ^ 2 + B * C).natDegree ≠ 2 * A.natDegree := by
      intro heq
      have hcoeff_ne : (x ^ 2 + B * C).coeff (2 * A.natDegree) ≠ 0 := by
        rw [← heq]
        exact Polynomial.leadingCoeff_ne_zero.mpr hsum0
      exact hcoeff_ne hcoeff
    exact lt_of_le_of_ne hle hne
  by_cases hd0 : d = 0
  · exact ⟨x, d, hxd', Or.inl hd0⟩
  · have hmuldeg : (A * d).natDegree < 2 * A.natDegree := by
      simpa [hxd'] using hsumdeg
    rw [Polynomial.natDegree_mul hA0 hd0] at hmuldeg
    exact ⟨x, d, hxd', Or.inr (by omega)⟩

/-!
The no-common-sign condition already selects a cyclic pivot for the
equal-degree top-cancellation lemma.  Since all three leading coefficients are
nonzero, failure of a common positive/negative sign at `+∞` forces an opposite
sign pair among them.
-/

theorem polynomialTernaryNoCommonStrictSignAtInfinity_cyclic_opposite_leadingCoeff
    [LinearOrder R] [Field R] [IsStrictOrderedRing R]
    {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hno : ¬ PolynomialTernaryCommonStrictSignAtInfinity A B C) :
    ∃ Ap Bp Cp : Polynomial R,
      ((Ap = A ∧ Bp = B ∧ Cp = C) ∨
        (Ap = B ∧ Bp = C ∧ Cp = A) ∨
          (Ap = C ∧ Bp = A ∧ Cp = B)) ∧
        Bp.leadingCoeff * Cp.leadingCoeff < 0 := by
  have hAlc : A.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hA0
  have hBlc : B.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hB0
  have hClc : C.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hC0
  by_contra hnot
  have hABnonneg : 0 ≤ A.leadingCoeff * B.leadingCoeff := by
    apply le_of_not_gt
    intro hlt
    apply hnot
    exact ⟨C, A, B, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hlt⟩
  have hACnonneg : 0 ≤ A.leadingCoeff * C.leadingCoeff := by
    apply le_of_not_gt
    intro hlt
    apply hnot
    exact ⟨B, C, A, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), by simpa [mul_comm] using hlt⟩
  have hBCnonneg : 0 ≤ B.leadingCoeff * C.leadingCoeff := by
    apply le_of_not_gt
    intro hlt
    apply hnot
    exact ⟨A, B, C, Or.inl ⟨rfl, rfl, rfl⟩, hlt⟩
  rcases lt_or_gt_of_ne hAlc with hAneg | hApos
  · have hBneg : B.leadingCoeff < 0 := by
      rcases lt_or_gt_of_ne hBlc with hBneg | hBpos
      · exact hBneg
      · exfalso
        nlinarith
    have hCneg : C.leadingCoeff < 0 := by
      rcases lt_or_gt_of_ne hClc with hCneg | hCpos
      · exact hCneg
      · exfalso
        nlinarith
    apply hno
    left
    right
    exact ⟨hAneg, hBneg, hCneg⟩
  · have hBpos : 0 < B.leadingCoeff := by
      rcases lt_or_gt_of_ne hBlc with hBneg | hBpos
      · exfalso
        nlinarith
      · exact hBpos
    have hCpos : 0 < C.leadingCoeff := by
      rcases lt_or_gt_of_ne hClc with hCneg | hCpos
      · exfalso
        nlinarith
      · exact hCpos
    apply hno
    left
    left
    exact ⟨hApos, hBpos, hCpos⟩

/-!
The package returned after choosing a pivot is named separately so that the
cyclic wrapper below can expose the orientation and the recursive state without
duplicating the long local/finite interface in every branch.
-/

def PolynomialTernaryClearedQuaternionSplitPivotSuccessor
    [Field R] {A B C Ap Bp Cp : Polynomial R} : Prop :=
  ∃ d D E : Polynomial R, ∃ s : SquarefreeGcdSplit D E,
    d ≠ 0 ∧ d.natDegree < Ap.natDegree ∧
      RatFunc.PolynomialLegendreLocalConditions s.G s.C₁ s.B₁ ∧
      Squarefree s.C₁ ∧ Squarefree s.B₁ ∧ Squarefree s.G ∧
        IsCoprime s.C₁ s.B₁ ∧ IsCoprime s.C₁ s.G ∧
          IsCoprime s.B₁ s.G ∧
            RatFunc.PolynomialLegendreWholeModConditions s.C₁ s.B₁ s.G ∧
              PolynomialTernaryQuaternionFiniteResiduesTrivialFor
                (PolynomialTernaryFiniteTameResidueTrivial s.C₁ s.B₁ s.G)
                s.C₁ s.B₁ s.G ∧
                (RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
                  RatFunc.PolynomialTernaryClearedQuaternionSplit s.C₁ s.B₁ s.G) ∧
                  (RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
                    RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
                      s.C₁ s.B₁ s.G) ∧
                    s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree ≤
                        Bp.natDegree + Cp.natDegree + d.natDegree ∧
                      s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree <
                        A.natDegree + B.natDegree + C.natDegree

/-!
The top-cancelled witness can now be consumed by the existing weighted and
arbitrary-right normalizer.  This is the equal-degree endpoint for an already
oriented pivot: the zero quotient is terminal, while the nonzero quotient is
strictly below the pivot, so the normalized successor has an unconditional
strict total-degree drop.
-/

theorem polynomialTernaryClearedQuaternionSplit_equal_degree_top_cancelled_right
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (heqAB : A.natDegree = B.natDegree)
    (heqBC : B.natDegree = C.natDegree)
    (hAdeg : 0 < A.natDegree)
    (hwhole : RatFunc.PolynomialLegendreWholeModConditions A B C)
    (hAsq : Squarefree A) (hBsq : Squarefree B) (hCsq : Squarefree C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hBC : IsCoprime B C)
    (hreal : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C)
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, v} R)
    (hneg : B.leadingCoeff * C.leadingCoeff < 0) :
    RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ∨
      PolynomialTernaryClearedQuaternionSplitPivotSuccessor.{u, v}
        (A := A) (B := B) (C := C) (Ap := A) (Bp := B) (Cp := C) := by
  rcases polynomialTernaryClearedQuaternionSplit_equal_degree_top_cancelled_witness
      hA0 hB0 hC0 heqAB heqBC hAdeg hneg hwhole with
    ⟨x, d, hxd, hdrop⟩
  by_cases hd0 : d = 0
  · left
    apply (RatFunc.polynomialTernaryClearedQuaternionSplit_descent hA0 hB0 hxd).mpr
    rw [hd0]
    exact quaternionSymbolSplit_of_right_eq_zero (by simp)
  · have hddeg : d.natDegree < A.natDegree := hdrop.resolve_left hd0
    rcases
        polynomialTernaryClearedQuaternionSplit_square_part_gcd_normalization_right
        (A := A) (B := B) (C := C) (d := d) (x := x)
        hA0 hB0 hC0 hd0 hAsq hBsq hCsq hAB hAC hBC hwhole hreal hrealization hxd with
      hsplit | hsucc
    · exact Or.inl hsplit
    · rcases hsucc with
        ⟨g, q, x₀, B₀, d₀, x₁, B₁, d₁, hg0, hq0, hgsq, hBfac, hdfac, hx₀,
          hidentity, hB₀fac, hd₀fac, hweighted, hB₁d₁, hB₁gC, Cs, c, hCs0,
          hc0, hCssq, hd₁fac, s, hlocal, hC₁sq, hB₁sq, hGsq, _hB₁G,
          hC₁B₁, hC₁G, hB₁G, hwholeN, hfiniteN, hsplitN, hrealN, hmeasureN,
          _hstrictN⟩
      have hmeasureFinal :
          s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree ≤
            B.natDegree + C.natDegree + d.natDegree := by
        exact hmeasureN
      have hstrictFinal :
          s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree <
            A.natDegree + B.natDegree + C.natDegree := by
        omega
      exact Or.inr ⟨d, B₁ * (g * C), B₁ * Cs, s, hd0, hddeg, hlocal,
        hC₁sq, hB₁sq, hGsq, hC₁B₁, hC₁G, hB₁G, hwholeN, hfiniteN,
        hsplitN, hrealN, hmeasureFinal, hstrictFinal⟩

/-!
Choose a strict pivot and run the recursive endpoint.  The endpoint itself is
cyclically invariant at the symbol and real-split layers; whole-modulus data is
permuted directly, and the finite package is generated by the endpoint rather
than assumed as an input.  If all three positive degrees coincide, the theorem
returns that exact residual branch instead of manufacturing a strict premise.
-/

theorem
    polynomialTernaryClearedQuaternionSplit_descent_wholeMod_normalized_right_pivot
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hwhole : RatFunc.PolynomialLegendreWholeModConditions A B C)
    (hAsq : Squarefree A) (hBsq : Squarefree B) (hCsq : Squarefree C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hBC : IsCoprime B C)
    (hreal : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C)
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, v} R)
    (hnonconstant : 0 < A.natDegree ∨ 0 < B.natDegree ∨ 0 < C.natDegree) :
    RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ∨
      (A.natDegree = B.natDegree ∧ B.natDegree = C.natDegree ∧
        0 < A.natDegree) ∨
      ∃ Ap Bp Cp : Polynomial R,
        ((Ap = A ∧ Bp = B ∧ Cp = C) ∨
          (Ap = B ∧ Bp = C ∧ Cp = A) ∨
            (Ap = C ∧ Bp = A ∧ Cp = B)) ∧
          0 < Ap.natDegree ∧
            Bp.natDegree + Cp.natDegree < 2 * Ap.natDegree ∧
              PolynomialTernaryClearedQuaternionSplitPivotSuccessor.{u, v}
                (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) := by
  rcases polynomialTernaryClearedQuaternionSplit_pivot_degree_choice
      hnonconstant with hEqual | hPivot
  · exact Or.inr (Or.inl hEqual)
  have run :
      ∀ {Ap Bp Cp : Polynomial R},
        Ap ≠ 0 → Bp ≠ 0 → Cp ≠ 0 →
          0 < Ap.natDegree →
            Bp.natDegree + Cp.natDegree < 2 * Ap.natDegree →
              RatFunc.PolynomialLegendreWholeModConditions Ap Bp Cp →
                Squarefree Ap → Squarefree Bp → Squarefree Cp →
                  IsCoprime Ap Bp → IsCoprime Ap Cp → IsCoprime Bp Cp →
                    RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
                      Ap Bp Cp →
                      (RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
                        RatFunc.PolynomialTernaryClearedQuaternionSplit Ap Bp Cp) →
                      (RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
                        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
                          Ap Bp Cp) →
                      Ap.natDegree + Bp.natDegree + Cp.natDegree =
                        A.natDegree + B.natDegree + C.natDegree →
                        RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ∨
                          PolynomialTernaryClearedQuaternionSplitPivotSuccessor.{u, v}
                            (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp)
                              (Cp := Cp) := by
    intro Ap Bp Cp hAp0 hBp0 hCp0 hApdeg hBpCpdeg hwholeP hAsp hBsp hCsp
      hABp hACp hBCp hrealP hsplitCycle hrealCycle htotal
    rcases
        polynomialTernaryClearedQuaternionSplit_descent_wholeMod_normalized_right
          (A := Ap) (B := Bp) (C := Cp) hAp0 hBp0 hCp0 hApdeg hBpCpdeg hwholeP
          hAsp hBsp hCsp hABp hACp hBCp hrealP hrealization with
      hsplit | hsucc
    · exact Or.inl (hsplitCycle.mpr hsplit)
    · right
      rcases hsucc with
        ⟨d, D, E, s, hd0, hddeg, hlocal, hC₁sq, hB₁sq, hGsq,
          hC₁B₁, hC₁G, hB₁G, hwholeN, hfiniteN, hsplitN, hrealN,
          hmeasureN, hstrictN⟩
      refine ⟨d, D, E, s, hd0, hddeg, hlocal, hC₁sq, hB₁sq, hGsq,
        hC₁B₁, hC₁G, hB₁G, hwholeN, hfiniteN,
        hsplitCycle.trans hsplitN, hrealCycle.trans hrealN, hmeasureN, ?_⟩
      omega
  rcases hPivot with ⟨Ap, Bp, Cp, horient, hApdeg, hBpCpdeg⟩
  rcases horient with horig | hcycle | hcycle
  · have hAp0 : Ap ≠ 0 := by rw [horig.1]; exact hA0
    have hBp0 : Bp ≠ 0 := by rw [horig.2.1]; exact hB0
    have hCp0 : Cp ≠ 0 := by rw [horig.2.2]; exact hC0
    have hrealP : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
        Ap Bp Cp := by
      rw [horig.1, horig.2.1, horig.2.2]
      exact hreal
    have hsplitCycle :
        RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
          RatFunc.PolynomialTernaryClearedQuaternionSplit Ap Bp Cp := by
      simp only [horig.1, horig.2.1, horig.2.2]
    have hrealCycle :
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
          RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} Ap Bp Cp := by
      simp only [horig.1, horig.2.1, horig.2.2]
    have htotal : Ap.natDegree + Bp.natDegree + Cp.natDegree =
        A.natDegree + B.natDegree + C.natDegree := by
      simp only [horig.1, horig.2.1, horig.2.2]
    have hwholeP : RatFunc.PolynomialLegendreWholeModConditions Ap Bp Cp := by
      rw [horig.1, horig.2.1, horig.2.2]
      exact hwhole
    have hAsP : Squarefree Ap := by rw [horig.1]; exact hAsq
    have hBsP : Squarefree Bp := by rw [horig.2.1]; exact hBsq
    have hCsP : Squarefree Cp := by rw [horig.2.2]; exact hCsq
    have hABP : IsCoprime Ap Bp := by rw [horig.1, horig.2.1]; exact hAB
    have hACP : IsCoprime Ap Cp := by rw [horig.1, horig.2.2]; exact hAC
    have hBCP : IsCoprime Bp Cp := by rw [horig.2.1, horig.2.2]; exact hBC
    rcases run (Ap := Ap) (Bp := Bp) (Cp := Cp) hAp0 hBp0 hCp0 hApdeg
        hBpCpdeg hwholeP hAsP hBsP hCsP hABP hACP hBCP hrealP hsplitCycle hrealCycle
        htotal with hsplit | hsucc
    · exact Or.inl hsplit
    · exact Or.inr (Or.inr ⟨Ap, Bp, Cp, Or.inl horig, hApdeg, hBpCpdeg, hsucc⟩)
  · have hAp0 : Ap ≠ 0 := by rw [hcycle.1]; exact hB0
    have hBp0 : Bp ≠ 0 := by rw [hcycle.2.1]; exact hC0
    have hCp0 : Cp ≠ 0 := by rw [hcycle.2.2]; exact hA0
    have hwholeCycle : RatFunc.PolynomialLegendreWholeModConditions B C A :=
      ⟨by simpa [mul_comm] using hwhole.2.1,
        by simpa [mul_comm] using hwhole.2.2,
        by simpa [mul_comm] using hwhole.1⟩
    have hwholeP : RatFunc.PolynomialLegendreWholeModConditions Ap Bp Cp := by
      simpa only [hcycle.1, hcycle.2.1, hcycle.2.2] using hwholeCycle
    have hrealCycleIff :
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
          RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} B C A :=
      RatFunc.polynomialTernaryClearedQuaternionRealSplit_cyclic_iff
        (R := R) (A := A) (B := B) (C := C) hA0 hB0
    have hrealP₀ :
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} B C A := by
      exact hrealCycleIff.mp hreal
    have hrealP : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
        Ap Bp Cp := by
      rw [hcycle.1, hcycle.2.1, hcycle.2.2]
      exact hrealP₀
    have hsplitCycle :=
      (RatFunc.polynomialTernaryClearedQuaternionSplit_cyclic_iff
        (R := R) (A := A) (B := B) (C := C) hA0 hB0)
    have hsplitP : RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
        RatFunc.PolynomialTernaryClearedQuaternionSplit Ap Bp Cp := by
      simpa only [hcycle.1, hcycle.2.1, hcycle.2.2] using hsplitCycle
    have hrealIff :
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
          RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} Ap Bp Cp := by
      simpa only [hcycle.1, hcycle.2.1, hcycle.2.2] using hrealCycleIff
    have htotal : Ap.natDegree + Bp.natDegree + Cp.natDegree =
        A.natDegree + B.natDegree + C.natDegree := by
      simp only [hcycle.1, hcycle.2.1, hcycle.2.2]
      omega
    have hAsP : Squarefree Ap := by rw [hcycle.1]; exact hBsq
    have hBsP : Squarefree Bp := by rw [hcycle.2.1]; exact hCsq
    have hCsP : Squarefree Cp := by rw [hcycle.2.2]; exact hAsq
    have hABP : IsCoprime Ap Bp := by rw [hcycle.1, hcycle.2.1]; exact hBC
    have hACP : IsCoprime Ap Cp := by rw [hcycle.1, hcycle.2.2]; exact hAB.symm
    have hBCP : IsCoprime Bp Cp := by rw [hcycle.2.1, hcycle.2.2]; exact hAC.symm
    rcases run (Ap := Ap) (Bp := Bp) (Cp := Cp) hAp0 hBp0 hCp0 hApdeg
        hBpCpdeg hwholeP hAsP hBsP hCsP hABP hACP hBCP hrealP hsplitP
        hrealIff htotal with
      hsplit | hsucc
    · exact Or.inl hsplit
    · exact Or.inr (Or.inr ⟨Ap, Bp, Cp, Or.inr (Or.inl hcycle), hApdeg, hBpCpdeg,
        hsucc⟩)
  · have hAp0 : Ap ≠ 0 := by rw [hcycle.1]; exact hC0
    have hBp0 : Bp ≠ 0 := by rw [hcycle.2.1]; exact hA0
    have hCp0 : Cp ≠ 0 := by rw [hcycle.2.2]; exact hB0
    have hwholeCycle : RatFunc.PolynomialLegendreWholeModConditions C A B :=
      ⟨by simpa [mul_comm] using hwhole.2.2,
        by simpa [mul_comm] using hwhole.1,
        by simpa [mul_comm] using hwhole.2.1⟩
    have hwholeP : RatFunc.PolynomialLegendreWholeModConditions Ap Bp Cp := by
      simpa only [hcycle.1, hcycle.2.1, hcycle.2.2] using hwholeCycle
    have hrealCycle₁ :
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
          RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} B C A :=
      RatFunc.polynomialTernaryClearedQuaternionRealSplit_cyclic_iff
        (R := R) (A := A) (B := B) (C := C) hA0 hB0
    have hrealCycle₂ :
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} B C A ↔
          RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} C A B :=
      RatFunc.polynomialTernaryClearedQuaternionRealSplit_cyclic_iff
        (R := R) (A := B) (B := C) (C := A) hB0 hC0
    have hrealCycle := hrealCycle₁.trans hrealCycle₂
    have hrealP₀ :
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} C A B := by
      exact hrealCycle.mp hreal
    have hrealP : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
        Ap Bp Cp := by
      rw [hcycle.1, hcycle.2.1, hcycle.2.2]
      exact hrealP₀
    have hsplitCycle₁ :=
      (RatFunc.polynomialTernaryClearedQuaternionSplit_cyclic_iff
        (R := R) (A := A) (B := B) (C := C) hA0 hB0)
    have hsplitCycle₂ :=
      (RatFunc.polynomialTernaryClearedQuaternionSplit_cyclic_iff
        (R := R) (A := B) (B := C) (C := A) hB0 hC0)
    have hsplitCycle := hsplitCycle₁.trans hsplitCycle₂
    have hsplitP : RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
        RatFunc.PolynomialTernaryClearedQuaternionSplit Ap Bp Cp := by
      simpa only [hcycle.1, hcycle.2.1, hcycle.2.2] using hsplitCycle
    have hrealIff :
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
          RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} Ap Bp Cp := by
      simpa only [hcycle.1, hcycle.2.1, hcycle.2.2] using hrealCycle
    have htotal : Ap.natDegree + Bp.natDegree + Cp.natDegree =
        A.natDegree + B.natDegree + C.natDegree := by
      simp only [hcycle.1, hcycle.2.1, hcycle.2.2]
      omega
    have hAsP : Squarefree Ap := by rw [hcycle.1]; exact hCsq
    have hBsP : Squarefree Bp := by rw [hcycle.2.1]; exact hAsq
    have hCsP : Squarefree Cp := by rw [hcycle.2.2]; exact hBsq
    have hABP : IsCoprime Ap Bp := by rw [hcycle.1, hcycle.2.1]; exact hAC.symm
    have hACP : IsCoprime Ap Cp := by rw [hcycle.1, hcycle.2.2]; exact hBC.symm
    have hBCP : IsCoprime Bp Cp := by rw [hcycle.2.1, hcycle.2.2]; exact hAB
    rcases run (Ap := Ap) (Bp := Bp) (Cp := Cp) hAp0 hBp0 hCp0 hApdeg
        hBpCpdeg hwholeP hAsP hBsP hCsP hABP hACP hBCP hrealP hsplitP
        hrealIff htotal with
      hsplit | hsucc
    · exact Or.inl hsplit
    · exact Or.inr (Or.inr ⟨Ap, Bp, Cp, Or.inr (Or.inr hcycle), hApdeg, hBpCpdeg,
        hsucc⟩)

/-!
Equal-degree consumer with the infinity sign bridge made explicit.  The
orientation theorem supplies a cyclic pivot whose two non-pivot leading
coefficients have opposite signs; the oriented top-cancel endpoint is then
transported back through the cyclic split/real equivalences.
-/

theorem polynomialTernaryClearedQuaternionSplit_equal_degree_pivot_of_noCommonInfinity
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (heqAB : A.natDegree = B.natDegree)
    (heqBC : B.natDegree = C.natDegree)
    (hAdeg : 0 < A.natDegree)
    (hwhole : RatFunc.PolynomialLegendreWholeModConditions A B C)
    (hAsq : Squarefree A) (hBsq : Squarefree B) (hCsq : Squarefree C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hBC : IsCoprime B C)
    (hreal : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C)
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, v} R)
    (hnoInf : ¬ PolynomialTernaryCommonStrictSignAtInfinity A B C) :
    RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ∨
      ∃ Ap Bp Cp : Polynomial R,
        ((Ap = A ∧ Bp = B ∧ Cp = C) ∨
          (Ap = B ∧ Bp = C ∧ Cp = A) ∨
            (Ap = C ∧ Bp = A ∧ Cp = B)) ∧
          PolynomialTernaryClearedQuaternionSplitPivotSuccessor.{u, v}
            (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) := by
  have lift :
      ∀ {Ap Bp Cp : Polynomial R},
        ((Ap = A ∧ Bp = B ∧ Cp = C) ∨
          (Ap = B ∧ Bp = C ∧ Cp = A) ∨
            (Ap = C ∧ Bp = A ∧ Cp = B)) →
        (RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
          RatFunc.PolynomialTernaryClearedQuaternionSplit Ap Bp Cp) →
        (RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
          RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} Ap Bp Cp) →
        Ap.natDegree + Bp.natDegree + Cp.natDegree =
          A.natDegree + B.natDegree + C.natDegree →
        PolynomialTernaryClearedQuaternionSplitPivotSuccessor.{u, v}
          (A := Ap) (B := Bp) (C := Cp) (Ap := Ap) (Bp := Bp) (Cp := Cp) →
        ∃ A' B' C' : Polynomial R,
          ((A' = A ∧ B' = B ∧ C' = C) ∨
            (A' = B ∧ B' = C ∧ C' = A) ∨
              (A' = C ∧ B' = A ∧ C' = B)) ∧
            PolynomialTernaryClearedQuaternionSplitPivotSuccessor.{u, v}
              (A := A) (B := B) (C := C) (Ap := A') (Bp := B') (Cp := C') := by
    intro Ap Bp Cp horient hsplitCycle hrealCycle htotal hsucc
    rcases hsucc with
      ⟨d, D, E, s, hd0, hddeg, hlocal, hC₁sq, hB₁sq, hGsq,
        hC₁B₁, hC₁G, hB₁G, hwholeN, hfiniteN, hsplitN, hrealN,
        hmeasureN, hstrictN⟩
    refine ⟨Ap, Bp, Cp, horient, ?_⟩
    refine ⟨d, D, E, s, hd0, hddeg, hlocal, hC₁sq, hB₁sq, hGsq,
      hC₁B₁, hC₁G, hB₁G, hwholeN, hfiniteN, hsplitCycle.trans hsplitN,
      hrealCycle.trans hrealN, hmeasureN, ?_⟩
    omega
  rcases polynomialTernaryNoCommonStrictSignAtInfinity_cyclic_opposite_leadingCoeff
      hA0 hB0 hC0 hnoInf with ⟨Ap, Bp, Cp, horient, hneg⟩
  rcases horient with horig | hcycle | hcycle
  · have hrealP : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
        Ap Bp Cp := by
      rw [horig.1, horig.2.1, horig.2.2]
      exact hreal
    have hwholeP : RatFunc.PolynomialLegendreWholeModConditions Ap Bp Cp := by
      rw [horig.1, horig.2.1, horig.2.2]
      exact hwhole
    have hAsP : Squarefree Ap := by rw [horig.1]; exact hAsq
    have hBsP : Squarefree Bp := by rw [horig.2.1]; exact hBsq
    have hCsP : Squarefree Cp := by rw [horig.2.2]; exact hCsq
    have hABP : IsCoprime Ap Bp := by rw [horig.1, horig.2.1]; exact hAB
    have hACP : IsCoprime Ap Cp := by rw [horig.1, horig.2.2]; exact hAC
    have hBCP : IsCoprime Bp Cp := by rw [horig.2.1, horig.2.2]; exact hBC
    have hAp0 : Ap ≠ 0 := by rw [horig.1]; exact hA0
    have hBp0 : Bp ≠ 0 := by rw [horig.2.1]; exact hB0
    have hCp0 : Cp ≠ 0 := by rw [horig.2.2]; exact hC0
    have hApdeg : 0 < Ap.natDegree := by rw [horig.1]; exact hAdeg
    have heqABP : Ap.natDegree = Bp.natDegree := by
      rw [horig.1, horig.2.1]
      exact heqAB
    have heqBCP : Bp.natDegree = Cp.natDegree := by
      rw [horig.2.1, horig.2.2]
      exact heqBC
    have hsplitCycle : RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
        RatFunc.PolynomialTernaryClearedQuaternionSplit Ap Bp Cp := by
      simp only [horig.1, horig.2.1, horig.2.2]
    have hrealCycle : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} Ap Bp Cp := by
      simp only [horig.1, horig.2.1, horig.2.2]
    have htotal : Ap.natDegree + Bp.natDegree + Cp.natDegree =
        A.natDegree + B.natDegree + C.natDegree := by
      simp only [horig.1, horig.2.1, horig.2.2]
    rcases
        polynomialTernaryClearedQuaternionSplit_equal_degree_top_cancelled_right
        (A := Ap) (B := Bp) (C := Cp) hAp0 hBp0 hCp0 heqABP heqBCP hApdeg
        hwholeP hAsP hBsP hCsP hABP hACP hBCP hrealP hrealization hneg with
      hsplit | hsucc
    · exact Or.inl (hsplitCycle.mpr hsplit)
    · exact Or.inr (lift (Ap := Ap) (Bp := Bp) (Cp := Cp) (Or.inl horig)
        hsplitCycle hrealCycle htotal hsucc)
  · have hwholeCycle : RatFunc.PolynomialLegendreWholeModConditions B C A :=
      ⟨by simpa [mul_comm] using hwhole.2.1,
        by simpa [mul_comm] using hwhole.2.2,
        by simpa [mul_comm] using hwhole.1⟩
    have hwholeP : RatFunc.PolynomialLegendreWholeModConditions Ap Bp Cp := by
      simpa only [hcycle.1, hcycle.2.1, hcycle.2.2] using hwholeCycle
    have hrealCycle : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} B C A :=
      RatFunc.polynomialTernaryClearedQuaternionRealSplit_cyclic_iff hA0 hB0
    have hrealP : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} Ap Bp Cp := by
      rw [hcycle.1, hcycle.2.1, hcycle.2.2]
      exact hrealCycle.mp hreal
    have hsplitCycle : RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
        RatFunc.PolynomialTernaryClearedQuaternionSplit Ap Bp Cp := by
      have hcyc := RatFunc.polynomialTernaryClearedQuaternionSplit_cyclic_iff
        (R := R) (A := A) (B := B) (C := C) hA0 hB0
      simpa only [hcycle.1, hcycle.2.1, hcycle.2.2] using hcyc
    have hrealIff : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} Ap Bp Cp := by
      simpa only [hcycle.1, hcycle.2.1, hcycle.2.2] using hrealCycle
    have hAsP : Squarefree Ap := by rw [hcycle.1]; exact hBsq
    have hBsP : Squarefree Bp := by rw [hcycle.2.1]; exact hCsq
    have hCsP : Squarefree Cp := by rw [hcycle.2.2]; exact hAsq
    have hABP : IsCoprime Ap Bp := by rw [hcycle.1, hcycle.2.1]; exact hBC
    have hACP : IsCoprime Ap Cp := by rw [hcycle.1, hcycle.2.2]; exact hAB.symm
    have hBCP : IsCoprime Bp Cp := by rw [hcycle.2.1, hcycle.2.2]; exact hAC.symm
    have hAp0 : Ap ≠ 0 := by rw [hcycle.1]; exact hB0
    have hBp0 : Bp ≠ 0 := by rw [hcycle.2.1]; exact hC0
    have hCp0 : Cp ≠ 0 := by rw [hcycle.2.2]; exact hA0
    have hBdeg : 0 < B.natDegree := by omega
    have hApdeg : 0 < Ap.natDegree := by rw [hcycle.1]; exact hBdeg
    have heqABP : Ap.natDegree = Bp.natDegree := by
      rw [hcycle.1, hcycle.2.1]
      exact heqBC
    have heqBCP : Bp.natDegree = Cp.natDegree := by
      rw [hcycle.2.1, hcycle.2.2]
      exact heqBC.symm.trans heqAB.symm
    have htotal : Ap.natDegree + Bp.natDegree + Cp.natDegree =
        A.natDegree + B.natDegree + C.natDegree := by
      simp only [hcycle.1, hcycle.2.1, hcycle.2.2]
      omega
    rcases
        polynomialTernaryClearedQuaternionSplit_equal_degree_top_cancelled_right
        (A := Ap) (B := Bp) (C := Cp) hAp0 hBp0 hCp0 heqABP heqBCP hApdeg
        hwholeP hAsP hBsP hCsP hABP hACP hBCP hrealP hrealization hneg with
      hsplit | hsucc
    · exact Or.inl (hsplitCycle.mpr hsplit)
    · exact Or.inr (lift (Ap := Ap) (Bp := Bp) (Cp := Cp) (Or.inr (Or.inl hcycle))
        hsplitCycle hrealIff htotal hsucc)
  · have hwholeCycle₁ : RatFunc.PolynomialLegendreWholeModConditions B C A :=
      ⟨by simpa [mul_comm] using hwhole.2.1,
        by simpa [mul_comm] using hwhole.2.2,
        by simpa [mul_comm] using hwhole.1⟩
    have hwholeCycle₂ : RatFunc.PolynomialLegendreWholeModConditions C A B :=
      ⟨by simpa [mul_comm] using hwhole.2.2,
        by simpa [mul_comm] using hwhole.1,
        by simpa [mul_comm] using hwhole.2.1⟩
    have hwholeP : RatFunc.PolynomialLegendreWholeModConditions Ap Bp Cp := by
      simpa only [hcycle.1, hcycle.2.1, hcycle.2.2] using hwholeCycle₂
    have hrealCycle₁ := RatFunc.polynomialTernaryClearedQuaternionRealSplit_cyclic_iff
      (R := R) (A := A) (B := B) (C := C) hA0 hB0
    have hrealCycle₂ := RatFunc.polynomialTernaryClearedQuaternionRealSplit_cyclic_iff
      (R := R) (A := B) (B := C) (C := A) hB0 hC0
    have hrealCycle := hrealCycle₁.trans hrealCycle₂
    have hrealP : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} Ap Bp Cp := by
      rw [hcycle.1, hcycle.2.1, hcycle.2.2]
      exact hrealCycle.mp hreal
    have hsplitCycle₁ := RatFunc.polynomialTernaryClearedQuaternionSplit_cyclic_iff
      (R := R) (A := A) (B := B) (C := C) hA0 hB0
    have hsplitCycle₂ := RatFunc.polynomialTernaryClearedQuaternionSplit_cyclic_iff
      (R := R) (A := B) (B := C) (C := A) hB0 hC0
    have hsplitCycle := hsplitCycle₁.trans hsplitCycle₂
    have hsplitIff : RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
        RatFunc.PolynomialTernaryClearedQuaternionSplit Ap Bp Cp := by
      simpa only [hcycle.1, hcycle.2.1, hcycle.2.2] using hsplitCycle
    have hrealIff : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} Ap Bp Cp := by
      simpa only [hcycle.1, hcycle.2.1, hcycle.2.2] using hrealCycle
    have hAsP : Squarefree Ap := by rw [hcycle.1]; exact hCsq
    have hBsP : Squarefree Bp := by rw [hcycle.2.1]; exact hAsq
    have hCsP : Squarefree Cp := by rw [hcycle.2.2]; exact hBsq
    have hABP : IsCoprime Ap Bp := by rw [hcycle.1, hcycle.2.1]; exact hAC.symm
    have hACP : IsCoprime Ap Cp := by rw [hcycle.1, hcycle.2.2]; exact hBC.symm
    have hBCP : IsCoprime Bp Cp := by rw [hcycle.2.1, hcycle.2.2]; exact hAB
    have hAp0 : Ap ≠ 0 := by rw [hcycle.1]; exact hC0
    have hBp0 : Bp ≠ 0 := by rw [hcycle.2.1]; exact hA0
    have hCp0 : Cp ≠ 0 := by rw [hcycle.2.2]; exact hB0
    have hCdeg : 0 < C.natDegree := by omega
    have hApdeg : 0 < Ap.natDegree := by rw [hcycle.1]; exact hCdeg
    have heqABP : Ap.natDegree = Bp.natDegree := by
      rw [hcycle.1, hcycle.2.1]
      exact heqBC.symm.trans heqAB.symm
    have heqBCP : Bp.natDegree = Cp.natDegree := by
      rw [hcycle.2.1, hcycle.2.2]
      exact heqAB
    have htotal : Ap.natDegree + Bp.natDegree + Cp.natDegree =
        A.natDegree + B.natDegree + C.natDegree := by
      simp only [hcycle.1, hcycle.2.1, hcycle.2.2]
      omega
    rcases
        polynomialTernaryClearedQuaternionSplit_equal_degree_top_cancelled_right
        (A := Ap) (B := Bp) (C := Cp) hAp0 hBp0 hCp0 heqABP heqBCP hApdeg
        hwholeP hAsP hBsP hCsP hABP hACP hBCP hrealP hrealization hneg with
      hsplit | hsucc
    · exact Or.inl (hsplitIff.mpr hsplit)
    · exact Or.inr (lift (Ap := Ap) (Bp := Bp) (Cp := Cp) (Or.inr (Or.inr hcycle))
        hsplitIff hrealIff htotal hsucc)

/--
Legendre finite local conditions plus the polynomial infinity condition give the
packaged residue-triviality input for the normalized polynomial quaternion
symbol.
-/
theorem polynomialTernaryQuaternionResiduesTrivialFor_of_legendreLocalConditions
    [LinearOrder R] [Field R] {A B C : Polynomial R}
    (hlocal : RatFunc.PolynomialLegendreLocalConditions A B C)
    (hinfty :
      PolynomialTernaryNoCommonStrictSignAtInfinity A B C
        (polynomialTernaryQuaternionCoeff A B)
        (polynomialTernaryQuaternionCoeff A C)) :
    PolynomialTernaryQuaternionResiduesTrivialFor
      (PolynomialTernaryFiniteResidueTrivial A B C)
      (PolynomialTernaryNoCommonStrictSignAtInfinity A B C) A B C :=
  ⟨polynomialTernaryFiniteResidueTrivial_of_legendreLocalConditions hlocal, hinfty⟩

/--
If infinity common signs are realized as orderings, then the absence of a
same-strict-sign ordering packages the finite Legendre conditions and the
infinity condition into the normalized polynomial quaternion residue input.
-/
theorem polynomialTernaryQuaternionResiduesTrivialFor_of_not_sameStrictSign
    [LinearOrder R] [Field R]
    (hinftyRealization : PolynomialTernaryInfinitySignRealization (R := R))
    {A B C : Polynomial R}
    (hlocal : RatFunc.PolynomialLegendreLocalConditions A B C)
    (hno :
      ¬ RatFunc.SameStrictSignOrdering
        (algebraMap (Polynomial R) (RatFunc R) A)
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C)) :
    PolynomialTernaryQuaternionResiduesTrivialFor
      (PolynomialTernaryFiniteResidueTrivial A B C)
      (PolynomialTernaryNoCommonStrictSignAtInfinity A B C) A B C :=
  polynomialTernaryQuaternionResiduesTrivialFor_of_legendreLocalConditions
    hlocal
    (polynomialTernaryNoCommonStrictSignAtInfinity_of_not_sameStrictSign
      hinftyRealization hno)

/--
Concrete Laurent-series version of the packaged polynomial quaternion residue
input.
-/
theorem polynomialTernaryQuaternionResiduesTrivialFor_laurentInfinity
    [LinearOrder R] [Field R] [IsStrictOrderedRing R]
    {A B C : Polynomial R}
    (hlocal : RatFunc.PolynomialLegendreLocalConditions A B C)
    (hno :
      ¬ RatFunc.SameStrictSignOrdering
        (algebraMap (Polynomial R) (RatFunc R) A)
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C)) :
    PolynomialTernaryQuaternionResiduesTrivialFor
      (PolynomialTernaryFiniteResidueTrivial A B C)
      (PolynomialTernaryNoCommonStrictSignAtInfinity A B C) A B C :=
  polynomialTernaryQuaternionResiduesTrivialFor_of_not_sameStrictSign
    polynomialTernaryInfinitySignRealization_laurentSeries hlocal hno

/--
For normalized ternary forms, local isotropy over every ordered real-closed
extension is exactly real split of the corresponding quaternion symbol.
-/
theorem ratFuncQuaternionRealSplit_iff_forall_ternary_isotropic_one [Field R]
    {b c : RatFunc R} :
    RatFuncQuaternionRealSplit.{u, v} (-b) (-c) ↔
      ∀ {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
          [Algebra (RatFunc R) K],
        Diagonal.TernaryIsotropic 1
          (algebraMap (RatFunc R) K b)
          (algebraMap (RatFunc R) K c) := by
  constructor
  · intro h K _ _ _ _ _
    have hsplit :
        QuaternionSymbolSplit (-(algebraMap (RatFunc R) K b))
          (-(algebraMap (RatFunc R) K c)) := by
      simpa using (h (K := K))
    exact Diagonal.ternary_isotropic_one_iff_quaternionSymbolSplit.mpr hsplit
  · intro h K _ _ _ _ _
    have htern :
        Diagonal.TernaryIsotropic 1
          (algebraMap (RatFunc R) K b)
          (algebraMap (RatFunc R) K c) :=
      h (K := K)
    have hsplit :
        QuaternionSymbolSplit (-(algebraMap (RatFunc R) K b))
          (-(algebraMap (RatFunc R) K c)) :=
      Diagonal.ternary_isotropic_one_iff_quaternionSymbolSplit.mp htern
    simpa using hsplit

/--
For an unnormalized ternary form with nonzero first coefficient, local isotropy
over every ordered real-closed extension is real split of the normalized
quaternion symbol.
-/
theorem ratFuncQuaternionRealSplit_iff_forall_ternary_isotropic_normalize_first [Field R]
    {a₀ a₁ a₂ : RatFunc R} (ha₀ : a₀ ≠ 0) :
    RatFuncQuaternionRealSplit.{u, v} (-(a₁ / a₀)) (-(a₂ / a₀)) ↔
      ∀ {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
          [Algebra (RatFunc R) K],
        Diagonal.TernaryIsotropic
          (algebraMap (RatFunc R) K a₀)
          (algebraMap (RatFunc R) K a₁)
          (algebraMap (RatFunc R) K a₂) := by
  constructor
  · intro h K _ _ _ _ _
    have ha₀K : algebraMap (RatFunc R) K a₀ ≠ 0 := by
      intro hzero
      exact ha₀ ((algebraMap (RatFunc R) K).injective (by simpa using hzero))
    have hsplit :
        QuaternionSymbolSplit
          (-(algebraMap (RatFunc R) K a₁ / algebraMap (RatFunc R) K a₀))
          (-(algebraMap (RatFunc R) K a₂ / algebraMap (RatFunc R) K a₀)) := by
      simpa using (h (K := K))
    exact
      (Diagonal.ternary_isotropic_iff_quaternionSymbolSplit_normalize_first
        ha₀K).mpr hsplit
  · intro h K _ _ _ _ _
    have ha₀K : algebraMap (RatFunc R) K a₀ ≠ 0 := by
      intro hzero
      exact ha₀ ((algebraMap (RatFunc R) K).injective (by simpa using hzero))
    have htern :
        Diagonal.TernaryIsotropic
          (algebraMap (RatFunc R) K a₀)
          (algebraMap (RatFunc R) K a₁)
          (algebraMap (RatFunc R) K a₂) :=
      h (K := K)
    have hsplit :
        QuaternionSymbolSplit
          (-(algebraMap (RatFunc R) K a₁ / algebraMap (RatFunc R) K a₀))
          (-(algebraMap (RatFunc R) K a₂ / algebraMap (RatFunc R) K a₀)) :=
      (Diagonal.ternary_isotropic_iff_quaternionSymbolSplit_normalize_first
        ha₀K).mp htern
    simpa using hsplit

end RatFuncWittLocalGlobal
