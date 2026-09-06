/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Ternary.Quaternion.Polynomial.RealSplit

/-!
# Polynomial quaternion detection
-/

namespace RatFuncWittLocalGlobal

universe u v

variable {R : Type u}

/--
Normalized-ordering-realization version of
`not_sameStrictSignOrdering_of_polynomialTernaryQuaternionRealSplit`.

A same-strict-sign ordering of `⟨A,B,C⟩` makes `B/A` and `C/A` positive.
Realizing that normalized pair in a real closed target contradicts real split
of the normalized quaternion symbol, since `⟨1,B/A,C/A⟩` would have all
coefficients positive there.
-/
theorem not_sameStrictSignOrdering_of_polynomialTernaryQuaternionRealSplit_normalized
    [Field R]
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, v} R)
    {A B C : Polynomial R}
    (_hA0 : A ≠ 0)
    (hreal :
      RatFuncQuaternionRealSplit.{u, v}
        (polynomialTernaryQuaternionCoeff A B)
        (polynomialTernaryQuaternionCoeff A C)) :
    ¬ RatFunc.SameStrictSignOrdering
      (algebraMap (Polynomial R) (RatFunc R) A)
      (algebraMap (Polynomial R) (RatFunc R) B)
      (algebraMap (Polynomial R) (RatFunc R) C) := by
  let φ : Polynomial R →+* RatFunc R := algebraMap (Polynomial R) (RatFunc R)
  intro hsame
  have hobs :
      RatFunc.NormalizedOrderingObstruction (φ B / φ A) (φ C / φ A) :=
    RatFunc.normalizedOrderingObstruction_of_sameStrictSign_div
      (by simpa [φ] using hsame)
  rcases hrealization (φ B / φ A) (φ C / φ A) hobs with ⟨w⟩
  let _ := w.field
  let _ := w.linearOrder
  let _ := w.strictOrdered
  let _ := w.realClosed
  let _ := w.algebra
  have hreal' :
      RatFuncQuaternionRealSplit.{u, v} (-(φ B / φ A)) (-(φ C / φ A)) := by
    intro K _ _ _ _ _
    have hK := hreal (K := K)
    simpa [φ, polynomialTernaryQuaternionCoeff, polynomialTernaryQuaternionCoeff] using hK
  have hlocal :
      ∀ {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
          [Algebra (RatFunc R) K],
        Diagonal.TernaryIsotropic 1
          (algebraMap (RatFunc R) K (φ B / φ A))
          (algebraMap (RatFunc R) K (φ C / φ A)) :=
    (ratFuncQuaternionRealSplit_iff_forall_ternary_isotropic_one
      (R := R) (b := φ B / φ A) (c := φ C / φ A)).mp hreal'
  have htern :
      Diagonal.TernaryIsotropic 1
        (algebraMap (RatFunc R) w.K (φ B / φ A))
        (algebraMap (RatFunc R) w.K (φ C / φ A)) :=
    hlocal (K := w.K)
  have hnonpos :
      algebraMap (RatFunc R) w.K (φ B / φ A) ≤ 0 ∨
        algebraMap (RatFunc R) w.K (φ C / φ A) ≤ 0 :=
    (Diagonal.ternary_isotropic_one_iff
      (algebraMap (RatFunc R) w.K (φ B / φ A))
      (algebraMap (RatFunc R) w.K (φ C / φ A))).mp htern
  rcases hnonpos with hb | hc
  · exact (not_le_of_gt w.pos_left) hb
  · exact (not_le_of_gt w.pos_right) hc

/-!
Complete the cyclic pivot step by deriving the explicit infinity no-common-sign
hypothesis from cleared real split.  The earlier pivot theorem handles the
strict-degree cases; the equal-degree branch uses the top-cancel endpoint and
the sign orientation bridge.
-/

theorem
    polynomialTernaryClearedQuaternionSplit_descent_wholeMod_normalized_right_pivot_complete
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
      ∃ Ap Bp Cp : Polynomial R,
        ((Ap = A ∧ Bp = B ∧ Cp = C) ∨
          (Ap = B ∧ Bp = C ∧ Cp = A) ∨
            (Ap = C ∧ Bp = A ∧ Cp = B)) ∧
          PolynomialTernaryClearedQuaternionSplitPivotSuccessor.{u, v}
            (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) := by
  have hclass := polynomialTernaryQuaternion_squareClass_cleared
    (R := R) (A := A) (B := B) (C := C) hA0
  rcases hclass with ⟨s, t, hs, ht, hp, hq⟩
  have hclass' : RatFuncQuaternionSquareClass
      (algebraMap (Polynomial R) (RatFunc R) (-(A * B)))
      (algebraMap (Polynomial R) (RatFunc R) (-(A * C)))
      (polynomialTernaryQuaternionCoeff A B)
      (polynomialTernaryQuaternionCoeff A C) := by
    refine ⟨s⁻¹, t⁻¹, inv_ne_zero hs, inv_ne_zero ht, ?_, ?_⟩
    · rw [hp]
      field_simp
    · rw [hq]
      field_simp
  have hrealN : RatFuncQuaternionRealSplit.{u, v}
      (polynomialTernaryQuaternionCoeff A B)
      (polynomialTernaryQuaternionCoeff A C) := by
    exact ratFuncQuaternionSquareClass_transfers_realSplit hclass' hreal
  have hnoSame : ¬ RatFunc.SameStrictSignOrdering
      (algebraMap (Polynomial R) (RatFunc R) A)
      (algebraMap (Polynomial R) (RatFunc R) B)
      (algebraMap (Polynomial R) (RatFunc R) C) :=
    not_sameStrictSignOrdering_of_polynomialTernaryQuaternionRealSplit_normalized
      hrealization hA0 hrealN
  have hnoInf : ¬ PolynomialTernaryCommonStrictSignAtInfinity A B C :=
    polynomialTernaryNoCommonStrictSignAtInfinity_of_not_sameStrictSign
      polynomialTernaryInfinitySignRealization_laurentSeries hnoSame
  by_cases hABeq : A.natDegree = B.natDegree
  · by_cases hBCeq : B.natDegree = C.natDegree
    · have hAdeg : 0 < A.natDegree := by
        rcases hnonconstant with hA | hB | hC <;> omega
      exact polynomialTernaryClearedQuaternionSplit_equal_degree_pivot_of_noCommonInfinity
        hA0 hB0 hC0 hABeq hBCeq hAdeg hwhole hAsq hBsq hCsq hAB hAC hBC hreal
        hrealization hnoInf
    · rcases
        polynomialTernaryClearedQuaternionSplit_descent_wholeMod_normalized_right_pivot
        hA0 hB0 hC0 hwhole hAsq hBsq hCsq hAB hAC hBC hreal hrealization hnonconstant with
      hsplit | heq | hsucc
      · exact Or.inl hsplit
      · exact False.elim (hBCeq heq.2.1)
      · rcases hsucc with ⟨Ap, Bp, Cp, horient, _hApdeg, _hBpCpdeg, hsucc⟩
        exact Or.inr ⟨Ap, Bp, Cp, horient, hsucc⟩
  · rcases
      polynomialTernaryClearedQuaternionSplit_descent_wholeMod_normalized_right_pivot
      hA0 hB0 hC0 hwhole hAsq hBsq hCsq hAB hAC hBC hreal hrealization hnonconstant with
    hsplit | heq | hsucc
    · exact Or.inl hsplit
    · exact False.elim (hABeq heq.1)
    · rcases hsucc with ⟨Ap, Bp, Cp, horient, _hApdeg, _hBpCpdeg, hsucc⟩
      exact Or.inr ⟨Ap, Bp, Cp, horient, hsucc⟩

/-!
The constant terminal branch is elementary once the real-split hypothesis has
been transported back to the normalized symbol.  The resulting no-common-sign
condition rules out all three constants having one strict sign, so one of the
two cleared coefficients is a square over the real-closed base field.
-/

theorem polynomialTernaryClearedQuaternionSplit_constant_terminal
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hAdeg : A.natDegree = 0) (hBdeg : B.natDegree = 0)
    (hCdeg : C.natDegree = 0)
    (hreal : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C)
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, v} R) :
    RatFunc.PolynomialTernaryClearedQuaternionSplit A B C := by
  have hclass := polynomialTernaryQuaternion_squareClass_cleared
    (R := R) (A := A) (B := B) (C := C) hA0
  rcases hclass with ⟨s, t, hs, ht, hp, hq⟩
  have hclass' : RatFuncQuaternionSquareClass
      (algebraMap (Polynomial R) (RatFunc R) (-(A * B)))
      (algebraMap (Polynomial R) (RatFunc R) (-(A * C)))
      (polynomialTernaryQuaternionCoeff A B)
      (polynomialTernaryQuaternionCoeff A C) := by
    refine ⟨s⁻¹, t⁻¹, inv_ne_zero hs, inv_ne_zero ht, ?_, ?_⟩
    · rw [hp]
      field_simp
    · rw [hq]
      field_simp
  have hrealN : RatFuncQuaternionRealSplit.{u, v}
      (polynomialTernaryQuaternionCoeff A B)
      (polynomialTernaryQuaternionCoeff A C) := by
    exact ratFuncQuaternionSquareClass_transfers_realSplit hclass' hreal
  have hnoSame : ¬ RatFunc.SameStrictSignOrdering
      (algebraMap (Polynomial R) (RatFunc R) A)
      (algebraMap (Polynomial R) (RatFunc R) B)
      (algebraMap (Polynomial R) (RatFunc R) C) :=
    not_sameStrictSignOrdering_of_polynomialTernaryQuaternionRealSplit_normalized
      hrealization hA0 hrealN
  have hnoInf : ¬ PolynomialTernaryCommonStrictSignAtInfinity A B C :=
    polynomialTernaryNoCommonStrictSignAtInfinity_of_not_sameStrictSign
      polynomialTernaryInfinitySignRealization_laurentSeries hnoSame
  rcases Polynomial.natDegree_eq_zero.mp hAdeg with ⟨a, ha⟩
  rcases Polynomial.natDegree_eq_zero.mp hBdeg with ⟨b, hb⟩
  rcases Polynomial.natDegree_eq_zero.mp hCdeg with ⟨c, hc⟩
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hA0
    rw [← ha, ha0]
    simp
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hB0
    rw [← hb, hb0]
    simp
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hC0
    rw [← hc, hc0]
    simp
  have hnoSigns : ¬ ((0 < a ∧ 0 < b ∧ 0 < c) ∨
      (a < 0 ∧ b < 0 ∧ c < 0)) := by
    intro hs
    apply hnoInf
    rcases hs with hs | hs
    · left
      left
      have hApos : PolynomialPosAtPosInfinity A := by
        rw [← ha]
        simpa [PolynomialPosAtPosInfinity] using hs.1
      have hBpos : PolynomialPosAtPosInfinity B := by
        rw [← hb]
        simpa [PolynomialPosAtPosInfinity] using hs.2.1
      have hCpos : PolynomialPosAtPosInfinity C := by
        rw [← hc]
        simpa [PolynomialPosAtPosInfinity] using hs.2.2
      exact ⟨hApos, hBpos, hCpos⟩
    · left
      right
      have hAneg : PolynomialNegAtPosInfinity A := by
        rw [← ha]
        simpa [PolynomialNegAtPosInfinity] using hs.1
      have hBneg : PolynomialNegAtPosInfinity B := by
        rw [← hb]
        simpa [PolynomialNegAtPosInfinity] using hs.2.1
      have hCneg : PolynomialNegAtPosInfinity C := by
        rw [← hc]
        simpa [PolynomialNegAtPosInfinity] using hs.2.2
      exact ⟨hAneg, hBneg, hCneg⟩
  have hprod : 0 ≤ -(a * b) ∨ 0 ≤ -(a * c) := by
    rcases lt_or_gt_of_ne ha0 with haneg | hapos
    · rcases lt_or_gt_of_ne hb0 with hbneg | hbpos
      · rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
        · exfalso
          exact hnoSigns (Or.inr ⟨haneg, hbneg, hcneg⟩)
        · right
          nlinarith
      · left
        nlinarith
    · rcases lt_or_gt_of_ne hb0 with hbneg | hbpos
      · left
        nlinarith
      · rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
        · right
          nlinarith
        · exfalso
          exact hnoSigns (Or.inl ⟨hapos, hbpos, hcpos⟩)
  rcases hprod with hABnonneg | hACnonneg
  · have hsAB : IsSquare (-(a * b)) := IsSquare.of_nonneg hABnonneg
    rcases hsAB with ⟨r, hr⟩
    have hsABφ : IsSquare
        (algebraMap (Polynomial R) (RatFunc R) (-(A * B))) := by
      refine ⟨algebraMap R (RatFunc R) r, ?_⟩
      rw [← ha, ← hb]
      simpa [map_mul, map_neg, map_pow] using congrArg (algebraMap R (RatFunc R)) hr
    exact quaternionSymbolSplit_of_isSquare_left hsABφ
  · have hsAC : IsSquare (-(a * c)) := IsSquare.of_nonneg hACnonneg
    rcases hsAC with ⟨r, hr⟩
    have hsACφ : IsSquare
        (algebraMap (Polynomial R) (RatFunc R) (-(A * C))) := by
      refine ⟨algebraMap R (RatFunc R) r, ?_⟩
      rw [← ha, ← hc]
      simpa [map_mul, map_neg, map_pow] using congrArg (algebraMap R (RatFunc R)) hr
    exact quaternionSymbolSplit_of_isSquare_right hsACφ

/-!
The pivot endpoint now closes by genuine strong induction on the total degree.
The successor package carries the recursive real-split equivalence and the
strict total-degree bound, so no conditional residual branch remains.
-/

theorem polynomialTernaryClearedQuaternionSplit_of_wholeMod_realSplit
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hwhole : RatFunc.PolynomialLegendreWholeModConditions A B C)
    (hAsq : Squarefree A) (hBsq : Squarefree B) (hCsq : Squarefree C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hBC : IsCoprime B C)
    (hreal : RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C)
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, v} R) :
    RatFunc.PolynomialTernaryClearedQuaternionSplit A B C := by
  have hmain :
      ∀ n : Nat, ∀ (A B C : Polynomial R),
        A ≠ 0 → B ≠ 0 → C ≠ 0 →
        RatFunc.PolynomialLegendreWholeModConditions A B C →
        Squarefree A → Squarefree B → Squarefree C →
        IsCoprime A B → IsCoprime A C → IsCoprime B C →
        RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C →
        A.natDegree + B.natDegree + C.natDegree = n →
        RatFunc.PolynomialTernaryClearedQuaternionSplit A B C := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B C hA0 hB0 hC0 hwhole hAsq hBsq hCsq hAB hAC hBC hreal hN
      by_cases hzero : n = 0
      · have hAdeg : A.natDegree = 0 := by omega
        have hBdeg : B.natDegree = 0 := by omega
        have hCdeg : C.natDegree = 0 := by omega
        exact polynomialTernaryClearedQuaternionSplit_constant_terminal
          hA0 hB0 hC0 hAdeg hBdeg hCdeg hreal hrealization
      · have hnonconstant : 0 < A.natDegree ∨ 0 < B.natDegree ∨ 0 < C.natDegree := by
          omega
        rcases
            polynomialTernaryClearedQuaternionSplit_descent_wholeMod_normalized_right_pivot_complete
            hA0 hB0 hC0 hwhole hAsq hBsq hCsq hAB hAC hBC hreal hrealization hnonconstant with
          hsplit | ⟨Ap, Bp, Cp, horient, hsucc⟩
        · exact hsplit
        · rcases hsucc with
            ⟨d, D, E, s, hd0, hddeg, hlocal, hC₁sq, hB₁sq, hGsq,
              hC₁B₁, hC₁G, hB₁G, hwholeN, hfiniteN, hsplitN, hrealN,
              hmeasureN, hstrictN⟩
          have hC₁0 : s.C₁ ≠ 0 := hC₁sq.ne_zero
          have hB₁0 : s.B₁ ≠ 0 := hB₁sq.ne_zero
          have hG0 : s.G ≠ 0 := hGsq.ne_zero
          have hstrictN' :
              s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree < n := by
            omega
          have hsplitSmall :
              RatFunc.PolynomialTernaryClearedQuaternionSplit s.C₁ s.B₁ s.G :=
            ih _ hstrictN' s.C₁ s.B₁ s.G hC₁0 hB₁0 hG0 hwholeN hC₁sq hB₁sq
              hGsq hC₁B₁ hC₁G hB₁G (hrealN.mp hreal) rfl
          exact hsplitN.mpr hsplitSmall
  exact hmain (A.natDegree + B.natDegree + C.natDegree) A B C
    hA0 hB0 hC0 hwhole hAsq hBsq hCsq hAB hAC hBC hreal rfl

/-!
The strong-induction theorem is now a direct finite-residue criterion once the
normalized ordering realization is supplied: tame/component finite residues
assemble `WholeMod`, and normalized real split transports to the cleared form.
-/

theorem polynomialTernaryQuaternionFiniteSplitCriterion_of_normalizedOrderingRealization
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, u} R) :
    PolynomialTernaryQuaternionFiniteSplitCriterion (R := R) := by
  intro A B C hA0 hB0 hC0 hAsq hBsq hCsq hAB hAC hBC hfinite hreal
  have htame :
      PolynomialTernaryQuaternionFiniteResiduesTrivialFor
        (PolynomialTernaryFiniteTameResidueTrivial A B C) A B C :=
    (polynomialTernaryQuaternionFiniteResiduesTrivialFor_tame_iff_component
      hAB hAC hBC).mpr hfinite
  have hwhole : RatFunc.PolynomialLegendreWholeModConditions A B C :=
    polynomialTernaryFiniteTameResiduesTrivial_globalSquareMod
      hA0 hB0 hC0 hAsq hBsq hCsq hAB hAC hBC htame
  have hrealCleared :
      RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, u} A B C :=
    polynomialTernaryQuaternionRealSplit_cleared_of_normalized hA0 hreal
  have hsplitCleared :
      RatFunc.PolynomialTernaryClearedQuaternionSplit A B C :=
    polynomialTernaryClearedQuaternionSplit_of_wholeMod_realSplit
      hA0 hB0 hC0 hwhole hAsq hBsq hCsq hAB hAC hBC hrealCleared hrealization
  exact polynomialTernaryQuaternionSplit_of_cleared hA0 hsplitCleared

theorem polynomialTernaryQuaternionSplitCriterion_of_normalizedOrderingRealization
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, u} R) :
    PolynomialTernaryQuaternionSplitCriterion (R := R) :=
  polynomialTernaryQuaternionSplitCriterion_of_finiteCriterion
    (polynomialTernaryQuaternionFiniteSplitCriterion_of_normalizedOrderingRealization
      hrealization)

/--
The polynomial-specialized quaternion criterion turns the packaged residue input
and the no-common-strict-sign real-split input into a split normalized
quaternion symbol.
-/
theorem polynomialQuaternionSymbolSplit_of_polyQuaternionCriterion
    [LinearOrder R] [Field R]
    (hcriterion : PolynomialTernaryQuaternionSplitCriterion (R := R))
    {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hAsq : Squarefree A) (hBsq : Squarefree B) (hCsq : Squarefree C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hBC : IsCoprime B C)
    (hres :
      PolynomialTernaryQuaternionResiduesTrivialFor
        (PolynomialTernaryFiniteResidueTrivial A B C)
        (PolynomialTernaryNoCommonStrictSignAtInfinity A B C) A B C)
    (hno :
      ¬ RatFunc.SameStrictSignOrdering
        (algebraMap (Polynomial R) (RatFunc R) A)
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C)) :
    QuaternionSymbolSplit
      (polynomialTernaryQuaternionCoeff A B)
      (polynomialTernaryQuaternionCoeff A C) :=
  (hcriterion A B C hA0 hB0 hC0 hAsq hBsq hCsq hAB hAC hBC)
    hres
    (polynomialTernaryQuaternionRealSplit_of_not_sameStrictSign
      hA0 hB0 hC0 hno)

end RatFuncWittLocalGlobal
