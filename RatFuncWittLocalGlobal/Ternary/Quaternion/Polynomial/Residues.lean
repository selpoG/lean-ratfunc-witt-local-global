/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Ternary.Quaternion.Polynomial.Basic
import RatFuncWittLocalGlobal.Ternary.Quaternion.Criterion.Places

/-!
# Finite residues of polynomial quaternion symbols
-/

namespace RatFuncWittLocalGlobal

universe u v

variable {R : Type u}

/-- Residue-triviality predicate specialized to the normalized symbol of `⟨A,B,C⟩`. -/
def PolynomialTernaryQuaternionResiduesTrivial [Field R]
    (ResiduesTrivial : RatFunc R → RatFunc R → Prop)
    (A B C : Polynomial R) : Prop :=
  ResiduesTrivial (polynomialTernaryQuaternionCoeff A B) (polynomialTernaryQuaternionCoeff A C)

/--
Finite/infinity residue interface specialized to the normalized symbol of
`⟨A,B,C⟩`.
-/
def PolynomialTernaryQuaternionResiduesTrivialFor [Field R]
    (FiniteResidueTrivial : RatFunc R → RatFunc R → Polynomial R → Prop)
    (InfinityResidueTrivial : RatFunc R → RatFunc R → Prop)
    (A B C : Polynomial R) : Prop :=
  PolynomialTernaryQuaternionResiduesTrivial
    (RatFuncQuaternionResiduesTrivialFor FiniteResidueTrivial InfinityResidueTrivial)
    A B C

/--
Finite-residue interface specialized to the normalized symbol of `⟨A,B,C⟩`.
This is the polynomial-facing input used by the finite Faddeev route.
-/
def PolynomialTernaryQuaternionFiniteResiduesTrivialFor [Field R]
    (FiniteResidueTrivial : RatFunc R → RatFunc R → Polynomial R → Prop)
    (A B C : Polynomial R) : Prop :=
  PolynomialTernaryQuaternionResiduesTrivial
    (RatFuncQuaternionFiniteResiduesTrivialFor FiniteResidueTrivial)
    A B C

/--
Finite residue condition for the normalized symbol of a polynomial ternary form,
written in the same square-modulo language as the existing polynomial Legendre
local conditions.
-/
def PolynomialTernaryFiniteResidueTrivial [Field R]
    (A B C : Polynomial R) (_p _q : RatFunc R) (π : Polynomial R) : Prop :=
  (π ∣ A → IsSquareMod π (-(B * C))) ∧
    (π ∣ B → IsSquareMod π (-(A * C))) ∧
      (π ∣ C → IsSquareMod π (-(A * B)))

/--
Finite tame-residue representative for the normalized quaternion symbol
attached to `⟨A,B,C⟩` at the polynomial place `π`.

For `u = -B/A` and `v = -C/A`, the tame residue of `(u,v)` is represented,
up to squares, by `-B*C` when `π ∣ A`, by `-A*C` when `π ∣ B`, by `-A*B`
when `π ∣ C`, and by `1` when none of the three coefficients has a zero or
pole at `π`.
-/
noncomputable def PolynomialTernaryFiniteTameResidueClass [Field R]
    (A B C π : Polynomial R) : Polynomial R := by
  classical
  exact
    if π ∣ A then
      -(B * C)
    else if π ∣ B then
      -(A * C)
    else if π ∣ C then
      -(A * B)
    else
      1

/-- If the finite place divides the first coefficient, the tame residue is `-B*C`. -/
theorem polynomialTernaryFiniteTameResidueClass_of_dvd_left
    [Field R] {A B C π : Polynomial R} (hA : π ∣ A) :
    PolynomialTernaryFiniteTameResidueClass A B C π = -(B * C) := by
  simp [PolynomialTernaryFiniteTameResidueClass, hA]

/--
If the finite place does not divide the first coefficient but divides the
second, the tame residue is `-A*C`.
-/
theorem polynomialTernaryFiniteTameResidueClass_of_not_dvd_left_dvd_mid
    [Field R] {A B C π : Polynomial R} (hA : ¬ π ∣ A) (hB : π ∣ B) :
    PolynomialTernaryFiniteTameResidueClass A B C π = -(A * C) := by
  simp [PolynomialTernaryFiniteTameResidueClass, hA, hB]

/--
If the finite place divides only the third coefficient among the first two
tests, the tame residue is `-A*B`.
-/
theorem polynomialTernaryFiniteTameResidueClass_of_not_dvd_left_mid_dvd_right
    [Field R] {A B C π : Polynomial R}
    (hA : ¬ π ∣ A) (hB : ¬ π ∣ B) (hC : π ∣ C) :
    PolynomialTernaryFiniteTameResidueClass A B C π = -(A * B) := by
  simp [PolynomialTernaryFiniteTameResidueClass, hA, hB, hC]

/--
If the finite place divides none of the three coefficients, the tame residue
representative is `1`.
-/
theorem irreducible_not_dvd_right_of_isCoprime_of_dvd_left
    [Field R] {π A B : Polynomial R}
    (hπ : Irreducible π) (hAB : IsCoprime A B) (hπA : π ∣ A) :
    ¬ π ∣ B := by
  intro hπB
  rcases hπA with ⟨k, hk⟩
  have hcop : IsCoprime (π * k) B := by
    simpa [hk] using hAB
  have hπcop : IsCoprime π B :=
    IsCoprime.of_mul_left_left hcop
  exact (Irreducible.prime hπ).not_isUnit (hπcop.isUnit_of_dvd hπB)

/--
For a pairwise-coprime triple, an irreducible divisor of the second coefficient
selects the `-A*C` tame residue branch.
-/
def PolynomialTernaryFiniteTameResidueTrivial [Field R]
    (A B C : Polynomial R) (_p _q : RatFunc R) (π : Polynomial R) : Prop :=
  IsSquareMod π (PolynomialTernaryFiniteTameResidueClass A B C π)

/-!
Finite tame residues also transport to the unit-first cleared triple.  At a
place dividing `A`, the new `A*B`/`A*C` branch is zero modulo the place; away
from `A`, the old `B`/`C` branch is exactly the corresponding unit-first
branch.  This is the exceptional-factor step that cannot be obtained by a
bare square-class rewrite.
-/

theorem isSquareMod_neg_mid_mul_right_of_tameResidueTrivial_dvd_left
    [Field R] {A B C π : Polynomial R} {p q : RatFunc R}
    (hA : π ∣ A)
    (htriv : PolynomialTernaryFiniteTameResidueTrivial A B C p q π) :
    IsSquareMod π (-(B * C)) := by
  simpa [PolynomialTernaryFiniteTameResidueTrivial,
    polynomialTernaryFiniteTameResidueClass_of_dvd_left hA] using htriv

/-!
When a common factor is moved to the first coefficient, the finite residue at
that factor is exactly the missing square-modulus premise for the
common-factor whole-modulus transport.  The implication is deliberately
stated at the finite-residue layer: the Laurent-series constructions in this
file provide the infinity ordering, whereas finite places are represented by
the residue predicates below.
-/

theorem polynomialTernaryClearedQuaternionSplit_unit_first_gcdSplit_normalization_core
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hAsq : Squarefree A) (hBsq : Squarefree B) (hCsq : Squarefree C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C)
    (hreal :
      RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C)
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, v} R) :
    RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ∨
      ∃ s : SquarefreeGcdSplit (A * B) (A * C),
        RatFunc.PolynomialLegendreLocalConditions s.G s.C₁ s.B₁ ∧
          Squarefree s.C₁ ∧ Squarefree s.B₁ ∧ Squarefree s.G ∧
            A ∣ s.G ∧ IsCoprime s.C₁ s.B₁ ∧ IsCoprime s.C₁ s.G ∧
              IsCoprime s.B₁ s.G ∧
                (RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
                  RatFunc.PolynomialTernaryClearedQuaternionSplit s.C₁ s.B₁ s.G) ∧
                  (RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
                    RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
                      s.C₁ s.B₁ s.G) ∧
                    s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree ≤
                        A.natDegree + B.natDegree + C.natDegree ∧
                      (s.G.natDegree = A.natDegree ∨
                        s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree <
                          A.natDegree + B.natDegree + C.natDegree) := by
  let φ : Polynomial R →+* RatFunc R := algebraMap (Polynomial R) (RatFunc R)
  let P : Polynomial R := A * B
  let Q : Polynomial R := A * C
  have hP0 : P ≠ 0 := mul_ne_zero hA0 hB0
  have hQ0 : Q ≠ 0 := mul_ne_zero hA0 hC0
  have hPsq : Squarefree P := by
    exact squarefree_mul_iff.mpr ⟨hAB.isRelPrime, hAsq, hBsq⟩
  have hQsq : Squarefree Q := by
    exact squarefree_mul_iff.mpr ⟨hAC.isRelPrime, hAsq, hCsq⟩
  have hrealUnit :
      RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} 1 P Q := by
    exact (RatFunc.polynomialTernaryClearedQuaternionRealSplit_unit_first_iff
      (A := A) (B := B) (C := C)).mp hreal
  by_cases hsqP : IsSquare (-(φ P))
  · left
    apply (RatFunc.polynomialTernaryClearedQuaternionSplit_unit_first_iff
      (A := A) (B := B) (C := C)).mpr
    simpa [RatFunc.PolynomialTernaryClearedQuaternionSplit, P, Q, φ] using
      (quaternionSymbolSplit_of_isSquare_left hsqP)
  · by_cases hsqQ : IsSquare (-(φ Q))
    · left
      apply (RatFunc.polynomialTernaryClearedQuaternionSplit_unit_first_iff
        (A := A) (B := B) (C := C)).mpr
      simpa [RatFunc.PolynomialTernaryClearedQuaternionSplit, P, Q, φ] using
        (quaternionSymbolSplit_of_isSquare_right hsqQ)
    · have hno : ¬ RatFunc.NormalizedOrderingObstruction (φ P) (φ Q) := by
        intro hobs
        rcases hrealization (φ P) (φ Q) hobs with ⟨w⟩
        let _ := w.field
        let _ := w.linearOrder
        let _ := w.strictOrdered
        let _ := w.realClosed
        let _ := w.algebra
        have hreal' :
            RatFuncQuaternionRealSplit.{u, v} (-(φ P)) (-(φ Q)) := by
          intro K _ _ _ _ _
          have hK := hrealUnit (K := K)
          simpa [RatFunc.PolynomialTernaryClearedQuaternionRealSplit, P, Q, φ] using hK
        have hsplitK := hreal' (K := w.K)
        have htern :
            Diagonal.TernaryIsotropic 1
              (algebraMap (RatFunc R) w.K (φ P))
              (algebraMap (RatFunc R) w.K (φ Q)) := by
          apply Diagonal.ternary_isotropic_one_iff_quaternionSymbolSplit.mpr
          simpa using hsplitK
        have hnonpos :=
          (Diagonal.ternary_isotropic_one_iff
            (algebraMap (RatFunc R) w.K (φ P))
            (algebraMap (RatFunc R) w.K (φ Q))).mp htern
        rcases hnonpos with hPnonpos | hQnonpos
        · exact (not_le_of_gt w.pos_left) hPnonpos
        · exact (not_le_of_gt w.pos_right) hQnonpos
      rcases
          RatFunc.squarefreeGcdLegendreLocalConditionsNoOrderingObstruction_of_realClosed
            (R := R) P Q hP0 hQ0 hPsq hQsq hno hsqP hsqQ with
        ⟨s, hlocal⟩
      have hC₁B₁ : IsCoprime s.C₁ s.B₁ := s.coprime_B₁_C₁.symm
      have hC₁G : IsCoprime s.C₁ s.G := s.coprime_G_C₁.symm
      have hB₁G : IsCoprime s.B₁ s.G := s.coprime_G_B₁.symm
      have hsplitUnit :
          RatFunc.PolynomialTernaryClearedQuaternionSplit (1 : Polynomial R) P Q ↔
            RatFunc.PolynomialTernaryClearedQuaternionSplit s.C₁ s.B₁ s.G := by
        have hsplitOld :
            RatFunc.PolynomialTernaryClearedQuaternionSplit (1 : Polynomial R)
                (s.G * s.C₁) (s.G * s.B₁) ↔
              RatFunc.PolynomialTernaryClearedQuaternionSplit s.C₁ s.B₁ s.G :=
          by
            simpa using
              (RatFunc.polynomialTernaryClearedQuaternionSplit_common_factor_cyclic_transport
                (A := (1 : Polynomial R)) (B := s.C₁) (C := s.B₁) (h := s.G)
                one_ne_zero s.C₁_ne_zero s.G_ne_zero)
        have hsplitSwap :
            RatFunc.PolynomialTernaryClearedQuaternionSplit (1 : Polynomial R) P Q ↔
              RatFunc.PolynomialTernaryClearedQuaternionSplit (1 : Polynomial R) Q P := by
          change QuaternionSymbolSplit
              (algebraMap (Polynomial R) (RatFunc R) (-(1 * P)))
                (algebraMap (Polynomial R) (RatFunc R) (-(1 * Q))) ↔
            QuaternionSymbolSplit
              (algebraMap (Polynomial R) (RatFunc R) (-(1 * Q)))
                (algebraMap (Polynomial R) (RatFunc R) (-(1 * P)))
          simpa using (quaternionSymbolSplit_comm
            (u := algebraMap (Polynomial R) (RatFunc R) (-(1 * P)))
            (v := algebraMap (Polynomial R) (RatFunc R) (-(1 * Q))))
        apply hsplitSwap.trans
        simpa [P, Q, s.hB, s.hC] using hsplitOld
      have hrealNew :
          RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} (1 : Polynomial R) P Q ↔
            RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
              s.C₁ s.B₁ s.G := by
        have hrealOld :
            RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} (1 : Polynomial R)
                (s.G * s.C₁) (s.G * s.B₁) ↔
              RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v}
                s.C₁ s.B₁ s.G :=
          by
            simpa using
              (RatFunc.polynomialTernaryClearedQuaternionRealSplit_common_factor_cyclic_transport
                (R := R) (A := (1 : Polynomial R)) (B := s.C₁) (C := s.B₁) (h := s.G)
                one_ne_zero s.C₁_ne_zero s.G_ne_zero)
        have hrealSwap :
            RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} (1 : Polynomial R) P Q ↔
              RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} (1 : Polynomial R)
                Q P := by
          change RatFuncQuaternionRealSplit.{u, v}
              (algebraMap (Polynomial R) (RatFunc R) (-(1 * P)))
                (algebraMap (Polynomial R) (RatFunc R) (-(1 * Q))) ↔
            RatFuncQuaternionRealSplit.{u, v}
              (algebraMap (Polynomial R) (RatFunc R) (-(1 * Q)))
                (algebraMap (Polynomial R) (RatFunc R) (-(1 * P)))
          simpa using (ratFuncQuaternionRealSplit_comm)
        apply hrealSwap.trans
        simpa [P, Q, s.hB, s.hC] using hrealOld
      right
      have hAP : A ∣ P := by
        refine ⟨B, ?_⟩
        simp [P]
      have hAQ : A ∣ Q := by
        refine ⟨C, ?_⟩
        simp [Q]
      have hAGB : A ∣ s.G * s.B₁ := by
        rw [← s.hB]
        exact hAP
      have hAGC : A ∣ s.G * s.C₁ := by
        rw [← s.hC]
        exact hAQ
      have hAG : A ∣ s.G := by
        rcases s.coprime_B₁_C₁ with ⟨u, v, huv⟩
        rcases hAGB with ⟨p, hp⟩
        rcases hAGC with ⟨q, hq⟩
        refine ⟨u * p + v * q, ?_⟩
        calc
          s.G = s.G * (u * s.B₁ + v * s.C₁) := by rw [huv, mul_one]
          _ = u * (s.G * s.B₁) + v * (s.G * s.C₁) := by ring
          _ = u * (A * p) + v * (A * q) := by rw [hp, hq]
          _ = A * (u * p + v * q) := by ring
      have hAdegG : A.natDegree ≤ s.G.natDegree :=
        Polynomial.natDegree_le_of_dvd hAG s.G_ne_zero
      have hPdeg : P.natDegree = s.G.natDegree + s.B₁.natDegree := by
        calc
          P.natDegree = (s.G * s.B₁).natDegree := congrArg Polynomial.natDegree s.hB
          _ = s.G.natDegree + s.B₁.natDegree :=
            Polynomial.natDegree_mul s.G_ne_zero s.B₁_ne_zero
      have hQdeg : Q.natDegree = s.G.natDegree + s.C₁.natDegree := by
        calc
          Q.natDegree = (s.G * s.C₁).natDegree := congrArg Polynomial.natDegree s.hC
          _ = s.G.natDegree + s.C₁.natDegree :=
            Polynomial.natDegree_mul s.G_ne_zero s.C₁_ne_zero
      have hmeasure :
          s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree + s.G.natDegree =
            P.natDegree + Q.natDegree := by
        rw [hPdeg, hQdeg]
        omega
      have hPdegOrig : P.natDegree = A.natDegree + B.natDegree :=
        Polynomial.natDegree_mul hA0 hB0
      have hQdegOrig : Q.natDegree = A.natDegree + C.natDegree :=
        Polynomial.natDegree_mul hA0 hC0
      have hmeasureOrig :
          s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree ≤
            A.natDegree + B.natDegree + C.natDegree := by
        omega
      have hstrictOrig :
          s.G.natDegree = A.natDegree ∨
            s.C₁.natDegree + s.B₁.natDegree + s.G.natDegree <
              A.natDegree + B.natDegree + C.natDegree := by
        by_cases heq : s.G.natDegree = A.natDegree
        · exact Or.inl heq
        · right
          omega
      have hsplitNew :
          RatFunc.PolynomialTernaryClearedQuaternionSplit A B C ↔
            RatFunc.PolynomialTernaryClearedQuaternionSplit s.C₁ s.B₁ s.G := by
        apply (RatFunc.polynomialTernaryClearedQuaternionSplit_unit_first_iff
          (A := A) (B := B) (C := C)).trans
        simpa [P, Q] using hsplitUnit
      have hrealNew' :
          RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} A B C ↔
            RatFunc.PolynomialTernaryClearedQuaternionRealSplit.{u, v} s.C₁ s.B₁ s.G := by
        apply (RatFunc.polynomialTernaryClearedQuaternionRealSplit_unit_first_iff
          (A := A) (B := B) (C := C)).trans
        simpa [P, Q] using hrealNew
      refine ⟨s, hlocal, s.squarefree_C₁, s.squarefree_B₁, ?_, hAG, hC₁B₁, hC₁G, hB₁G,
        hsplitNew, hrealNew', hmeasureOrig, hstrictOrig⟩
      exact s.squarefree_G

/-!
For the weighted successor, the exceptional `π ∣ g` place is controlled by the
old residue itself, rather than by identifying `g` with a cyclic gcd split.
old residue itself, rather than by identifying `g` with a cyclic gcd split.
The weighted identity gives
`A*d₁ - B₁*C = g*x₁²`; after multiplying by `A*B₁`, the old square class
`-(A*C)` and the new class `-(B₁*d₁)` differ by a `π`-multiple.  Cancelling
the square `A²` with `IsSquareMod.of_mul_square_of_isCoprime` is the exact
local preservation step needed by the weighted recursion.
-/

theorem isSquareMod_neg_left_mul_right_of_tameResidueTrivial_not_dvd_left_dvd_mid
    [Field R] {A B C π : Polynomial R} {p q : RatFunc R}
    (hA : ¬ π ∣ A) (hB : π ∣ B)
    (htriv : PolynomialTernaryFiniteTameResidueTrivial A B C p q π) :
    IsSquareMod π (-(A * C)) := by
  simpa [PolynomialTernaryFiniteTameResidueTrivial,
    polynomialTernaryFiniteTameResidueClass_of_not_dvd_left_dvd_mid hA hB] using htriv

/--
In the `π ∤ A`, `π ∤ B`, `π ∣ C` branch, tame-residue triviality gives
square-mod triviality of `-A*B`.
-/
theorem isSquareMod_neg_left_mul_mid_of_tameResidueTrivial_not_dvd_left_mid_dvd_right
    [Field R] {A B C π : Polynomial R} {p q : RatFunc R}
    (hA : ¬ π ∣ A) (hB : ¬ π ∣ B) (hC : π ∣ C)
    (htriv : PolynomialTernaryFiniteTameResidueTrivial A B C p q π) :
    IsSquareMod π (-(A * B)) := by
  simpa [PolynomialTernaryFiniteTameResidueTrivial,
    polynomialTernaryFiniteTameResidueClass_of_not_dvd_left_mid_dvd_right hA hB hC]
    using htriv

/--
For a pairwise-coprime triple, tame-residue triviality at an irreducible
divisor of the second coefficient gives square-mod triviality of `-A*C`.
-/
theorem isSquareMod_neg_left_mul_right_of_tameResidueTrivial_irreducible_dvd_mid
    [Field R] {A B C π : Polynomial R} {p q : RatFunc R}
    (hπ : Irreducible π) (hAB : IsCoprime A B) (hπB : π ∣ B)
    (htriv : PolynomialTernaryFiniteTameResidueTrivial A B C p q π) :
    IsSquareMod π (-(A * C)) :=
  isSquareMod_neg_left_mul_right_of_tameResidueTrivial_not_dvd_left_dvd_mid
    (irreducible_not_dvd_right_of_isCoprime_of_dvd_left hπ hAB.symm hπB)
    hπB htriv

/--
For a pairwise-coprime triple, tame-residue triviality at an irreducible
divisor of the third coefficient gives square-mod triviality of `-A*B`.
-/
theorem isSquareMod_neg_left_mul_mid_of_tameResidueTrivial_irreducible_dvd_right
    [Field R] {A B C π : Polynomial R} {p q : RatFunc R}
    (hπ : Irreducible π) (hAC : IsCoprime A C) (hBC : IsCoprime B C)
    (hπC : π ∣ C)
    (htriv : PolynomialTernaryFiniteTameResidueTrivial A B C p q π) :
    IsSquareMod π (-(A * B)) :=
  isSquareMod_neg_left_mul_mid_of_tameResidueTrivial_not_dvd_left_mid_dvd_right
    (irreducible_not_dvd_right_of_isCoprime_of_dvd_left hπ hAC.symm hπC)
    (irreducible_not_dvd_right_of_isCoprime_of_dvd_left hπ hBC.symm hπC)
    hπC htriv

/--
The componentwise finite residue conditions imply the single tame-residue
condition at the same finite place.
-/
theorem polynomialTernaryFiniteTameResidueTrivial_of_component
    [Field R] {A B C : Polynomial R} {p q : RatFunc R} {π : Polynomial R}
    (hfinite : PolynomialTernaryFiniteResidueTrivial A B C p q π) :
    PolynomialTernaryFiniteTameResidueTrivial A B C p q π := by
  by_cases hA : π ∣ A
  · simpa [PolynomialTernaryFiniteTameResidueTrivial,
      PolynomialTernaryFiniteTameResidueClass, hA] using hfinite.1 hA
  · by_cases hB : π ∣ B
    · simpa [PolynomialTernaryFiniteTameResidueTrivial,
        PolynomialTernaryFiniteTameResidueClass, hA, hB] using hfinite.2.1 hB
    · by_cases hC : π ∣ C
      · simpa [PolynomialTernaryFiniteTameResidueTrivial,
          PolynomialTernaryFiniteTameResidueClass, hA, hB, hC] using hfinite.2.2 hC
      · refine ⟨1, ?_⟩
        change π ∣ (1 : Polynomial R) ^ 2 -
          PolynomialTernaryFiniteTameResidueClass A B C π
        simp [PolynomialTernaryFiniteTameResidueClass, hA, hB, hC]

/--
For pairwise-coprime triples, tame-residue triviality at an irreducible finite
place gives back the componentwise finite residue conditions.
-/
theorem polynomialTernaryFiniteResidueTrivial_of_tameResidueTrivial
    [Field R] {A B C : Polynomial R} {p q : RatFunc R} {π : Polynomial R}
    (hπ : Irreducible π) (hAB : IsCoprime A B) (hAC : IsCoprime A C)
    (hBC : IsCoprime B C)
    (htriv : PolynomialTernaryFiniteTameResidueTrivial A B C p q π) :
    PolynomialTernaryFiniteResidueTrivial A B C p q π := by
  refine ⟨?_, ?_, ?_⟩
  · intro hπA
    exact isSquareMod_neg_mid_mul_right_of_tameResidueTrivial_dvd_left
      hπA htriv
  · intro hπB
    exact isSquareMod_neg_left_mul_right_of_tameResidueTrivial_irreducible_dvd_mid
      hπ hAB hπB htriv
  · intro hπC
    exact isSquareMod_neg_left_mul_mid_of_tameResidueTrivial_irreducible_dvd_right
      hπ hAC hBC hπC htriv

/--
For pairwise-coprime triples, the finite tame-residue package and the
componentwise finite-residue package are equivalent for the normalized symbol.
-/
theorem polynomialTernaryQuaternionFiniteResiduesTrivialFor_tame_iff_component
    [Field R] {A B C : Polynomial R}
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hBC : IsCoprime B C) :
    PolynomialTernaryQuaternionFiniteResiduesTrivialFor
        (PolynomialTernaryFiniteTameResidueTrivial A B C) A B C ↔
      PolynomialTernaryQuaternionFiniteResiduesTrivialFor
        (PolynomialTernaryFiniteResidueTrivial A B C) A B C := by
  constructor
  · intro htame π hπ
    exact polynomialTernaryFiniteResidueTrivial_of_tameResidueTrivial
      hπ hAB hAC hBC (htame π hπ)
  · intro hfinite π hπ
    exact polynomialTernaryFiniteTameResidueTrivial_of_component
      (hfinite π hπ)

/-!
The componentwise finite package is invariant under the square-factor
normalization of all three coefficients.  It is converted back to the tame
package only after the normalized cores' pairwise coprimality is supplied.
-/

theorem polynomialTernaryFiniteTameResiduesTrivial_globalSquareMod
    [Field R] {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hAsq : Squarefree A) (hBsq : Squarefree B) (hCsq : Squarefree C)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hBC : IsCoprime B C)
    (hfinite :
      PolynomialTernaryQuaternionFiniteResiduesTrivialFor
        (PolynomialTernaryFiniteTameResidueTrivial A B C) A B C) :
    RatFunc.PolynomialLegendreWholeModConditions A B C := by
  refine ⟨?_, ?_, ?_⟩
  · exact isSquareMod_of_forall_irreducible_dvd_of_squarefree hA0 hAsq
      (fun π hπ hπA =>
        isSquareMod_neg_mid_mul_right_of_tameResidueTrivial_dvd_left
          hπA (hfinite π hπ))
  · exact isSquareMod_of_forall_irreducible_dvd_of_squarefree hB0 hBsq
      (fun π hπ hπB =>
        isSquareMod_neg_left_mul_right_of_tameResidueTrivial_irreducible_dvd_mid
          hπ hAB hπB (hfinite π hπ))
  · exact isSquareMod_of_forall_irreducible_dvd_of_squarefree hC0 hCsq
      (fun π hπ hπC =>
        isSquareMod_neg_left_mul_mid_of_tameResidueTrivial_irreducible_dvd_right
          hπ hAC hBC hπC (hfinite π hπ))

/--
The assembled whole-modulus congruences immediately recover the usual
finite Legendre local-condition package.  This is the direct consumer bridge
for the global congruence theorem above.
-/
def PolynomialTernaryCommonStrictSignAtInfinity [LinearOrder R] [Ring R]
    (A B C : Polynomial R) : Prop :=
  ((PolynomialPosAtPosInfinity A ∧ PolynomialPosAtPosInfinity B ∧
      PolynomialPosAtPosInfinity C) ∨
    (PolynomialNegAtPosInfinity A ∧ PolynomialNegAtPosInfinity B ∧
      PolynomialNegAtPosInfinity C)) ∨
  ((PolynomialPosAtNegInfinity A ∧ PolynomialPosAtNegInfinity B ∧
      PolynomialPosAtNegInfinity C) ∨
    (PolynomialNegAtNegInfinity A ∧ PolynomialNegAtNegInfinity B ∧
      PolynomialNegAtNegInfinity C))

/--
Infinity-place condition for the normalized quaternion symbol of `⟨A,B,C⟩`.
It records that the two infinity orderings do not give a common strict sign for
the three polynomial coefficients.
-/
def PolynomialTernaryNoCommonStrictSignAtInfinity [LinearOrder R] [Field R]
    (A B C : Polynomial R) (_p _q : RatFunc R) : Prop :=
  ¬ PolynomialTernaryCommonStrictSignAtInfinity A B C

/--
Polynomial-specialized residue criterion for the normalized quaternion symbol
attached to a squarefree pairwise-coprime ternary polynomial form.

This is the current main polynomial target: for the normalized symbol attached
to `⟨A,B,C⟩`, prove that packaged finite/infinity residues and real split imply
global split.  It is deliberately stated only for that normalized symbol; the
finite and infinity predicates below do not classify arbitrary `p q`.
-/
def PolynomialTernaryQuaternionSplitCriterion
    [LinearOrder R] [Field R] : Prop :=
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
                      PolynomialTernaryQuaternionResiduesTrivialFor
                        (PolynomialTernaryFiniteResidueTrivial A B C)
                        (PolynomialTernaryNoCommonStrictSignAtInfinity A B C) A B C →
                        RatFuncQuaternionRealSplit.{u, u}
                          (polynomialTernaryQuaternionCoeff A B)
                          (polynomialTernaryQuaternionCoeff A C) →
                          QuaternionSymbolSplit
                            (polynomialTernaryQuaternionCoeff A B)
                            (polynomialTernaryQuaternionCoeff A C)

end RatFuncWittLocalGlobal
