/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Ternary.Reduction.Basic
import RatFuncWittLocalGlobal.Ternary.Legendre.ClearedBinary.Endpoint

/-!
# Polynomial normalization for the ternary local-global theorem

This module transports the normalized rational-function statement to
polynomial coefficients and connects it to the cleared-binary Legendre
interfaces.  The public normalized target is defined in `Ternary.Reduction.Basic`;
the intermediate polynomial formulations remain private to this module.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

/-- Internal polynomial-coefficient form of the normalized ternary statement. -/
private def PolynomialNormalizedTernaryLocalGlobal
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] : Prop :=
  ∀ B C : Polynomial R,
    NormalizedSignObstructionFree.{u, v}
      (algebraMap (Polynomial R) (RatFunc R) B)
      (algebraMap (Polynomial R) (RatFunc R) C) →
      Diagonal.TernaryIsotropic 1
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C)

/-- Internal regular polynomial form used by the squarefree reduction. -/
private def RegularPolynomialNormalizedTernaryLocalGlobal
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] : Prop :=
  ∀ B C : Polynomial R,
    B ≠ 0 →
      C ≠ 0 →
        NormalizedSignObstructionFree.{u, v}
          (algebraMap (Polynomial R) (RatFunc R) B)
          (algebraMap (Polynomial R) (RatFunc R) C) →
          Diagonal.TernaryIsotropic 1
            (algebraMap (Polynomial R) (RatFunc R) B)
            (algebraMap (Polynomial R) (RatFunc R) C)

private theorem regularPolynomialNormalizedTernaryLocalGlobal_of_polynomial
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hpoly : PolynomialNormalizedTernaryLocalGlobal.{u, v} R) :
    RegularPolynomialNormalizedTernaryLocalGlobal.{u, v} R := by
  intro B C _ _ hobs
  exact hpoly B C hobs

private theorem polynomialNormalizedTernaryLocalGlobal_of_regular
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hreg : RegularPolynomialNormalizedTernaryLocalGlobal.{u, v} R) :
    PolynomialNormalizedTernaryLocalGlobal.{u, v} R := by
  intro B C hobs
  by_cases hB : B = 0
  · subst B
    let a : Fin 3 → RatFunc R := ![1, 0, algebraMap (Polynomial R) (RatFunc R) C]
    have ha : Diagonal.Isotropic a :=
      Diagonal.isotropic_of_zero_coeff a (i := 1) (by simp [a])
    simpa [a] using (Diagonal.isotropic_fin_three_iff a).mp ha
  · by_cases hC : C = 0
    · subst C
      let a : Fin 3 → RatFunc R := ![1, algebraMap (Polynomial R) (RatFunc R) B, 0]
      have ha : Diagonal.Isotropic a :=
        Diagonal.isotropic_of_zero_coeff a (i := 2) (by simp [a])
      simpa [a] using (Diagonal.isotropic_fin_three_iff a).mp ha
    · exact hreg B C hB hC hobs

private theorem polynomial_ternary_isotropic_mul_square
    {R : Type u} [Field R] {B C S T : Polynomial R}
    (hS : S ≠ 0) (hT : T ≠ 0) :
    Diagonal.TernaryIsotropic 1
        (algebraMap (Polynomial R) (RatFunc R) (B * S ^ 2))
        (algebraMap (Polynomial R) (RatFunc R) (C * T ^ 2)) ↔
      Diagonal.TernaryIsotropic 1
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C) := by
  let s : RatFunc R := algebraMap (Polynomial R) (RatFunc R) S
  let t : RatFunc R := algebraMap (Polynomial R) (RatFunc R) T
  have hs : s ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hS
  have ht : t ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hT
  simpa [s, t, map_mul, map_pow] using
    (Diagonal.ternary_isotropic_mul_square (F := RatFunc R)
      (a₀ := 1)
      (a₁ := algebraMap (Polynomial R) (RatFunc R) B)
      (a₂ := algebraMap (Polynomial R) (RatFunc R) C)
      (u₀ := 1) (u₁ := s) (u₂ := t) one_ne_zero hs ht)

private theorem clearedBinaryOrSquareRight_mul_square
    {R : Type u} [Field R] {B C S T : Polynomial R}
    (hS : S ≠ 0) (hT : T ≠ 0) :
    ClearedBinaryOrSquareRight R (B * S ^ 2) (C * T ^ 2) ↔
      ClearedBinaryOrSquareRight R B C := by
  calc
    ClearedBinaryOrSquareRight R (B * S ^ 2) (C * T ^ 2) ↔
        Diagonal.TernaryIsotropic 1
          (algebraMap (Polynomial R) (RatFunc R) (B * S ^ 2))
          (algebraMap (Polynomial R) (RatFunc R) (C * T ^ 2)) :=
      clearedBinaryOrSquareRight_iff_ternary_isotropic _ _
    _ ↔ Diagonal.TernaryIsotropic 1
          (algebraMap (Polynomial R) (RatFunc R) B)
          (algebraMap (Polynomial R) (RatFunc R) C) :=
      polynomial_ternary_isotropic_mul_square
        (R := R) (B := B) (C := C) (S := S) (T := T) hS hT
    _ ↔ ClearedBinaryOrSquareRight R B C :=
      (clearedBinaryOrSquareRight_iff_ternary_isotropic B C).symm

private theorem clearedBinaryConstructionRightNoObstruction_of_squarefree
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hsqfree : SquarefreeClearedBinaryConstructionRightNoObstruction.{u, v} R) :
    ClearedBinaryConstructionRightNoObstruction.{u, v} R := by
  intro A D hA hD hno
  rcases exists_squarefree_mul_square_of_ne_zero hA with ⟨B, S, hB, hS, hBsq, hAeq⟩
  rcases exists_squarefree_mul_square_of_ne_zero hD with ⟨C, T, hC, hT, hCsq, hDeq⟩
  have hno_base :
      ¬ HasNormalizedSignObstruction.{u, v}
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C) := by
    intro hbad
    apply hno
    have hscaled :
        HasNormalizedSignObstruction.{u, v}
          (algebraMap (Polynomial R) (RatFunc R) (B * S ^ 2))
          (algebraMap (Polynomial R) (RatFunc R) (C * T ^ 2)) :=
      (hasNormalizedSignObstruction_polynomial_mul_square
        (R := R) (B := B) (C := C) (S := S) (T := T) hS hT).mpr hbad
    simpa [hAeq, hDeq] using hscaled
  have hbase : ClearedBinaryOrSquareRight R B C :=
    hsqfree B C hB hC hBsq hCsq hno_base
  have hscaled : ClearedBinaryOrSquareRight R (B * S ^ 2) (C * T ^ 2) :=
    (clearedBinaryOrSquareRight_mul_square
      (R := R) (B := B) (C := C) (S := S) (T := T) hS hT).mpr hbase
  simpa [hAeq, hDeq] using hscaled

private theorem clearedBinaryConstructionRightNoObstruction_iff_squarefree
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    ClearedBinaryConstructionRightNoObstruction.{u, v} R ↔
      SquarefreeClearedBinaryConstructionRightNoObstruction.{u, v} R := by
  constructor
  · intro h B C hB hC _ _ hno
    exact h B C hB hC hno
  · exact clearedBinaryConstructionRightNoObstruction_of_squarefree

private theorem polynomialNormalizedTernaryLocalGlobal_of_normalized
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hnorm : NormalizedTernaryLocalGlobal.{u, v} R) :
    PolynomialNormalizedTernaryLocalGlobal.{u, v} R := by
  intro B C hobs
  exact hnorm
    (algebraMap (Polynomial R) (RatFunc R) B)
    (algebraMap (Polynomial R) (RatFunc R) C)
    ((normalizedSignObstructionFree_iff_locallyIsotropic _ _).mp hobs)

private theorem normalizedTernaryLocalGlobal_of_polynomial
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hpoly : PolynomialNormalizedTernaryLocalGlobal.{u, v} R) :
    NormalizedTernaryLocalGlobal.{u, v} R := by
  intro b c hlocal
  let x : Fin 2 → RatFunc R := fun i => if i = 0 then b else c
  rcases exists_common_denominator (R := R) (ι := Fin 2) x with ⟨d, hd, hden⟩
  rcases hden 0 with ⟨B, hB⟩
  rcases hden 1 with ⟨C, hC⟩
  let D : RatFunc R := algebraMap (Polynomial R) (RatFunc R) d
  have hD : D ≠ 0 := by
    exact _root_.RatFunc.algebraMap_ne_zero hd
  have hb_rep : b = algebraMap (Polynomial R) (RatFunc R) B / D := by
    simpa [x, D] using hB
  have hc_rep : c = algebraMap (Polynomial R) (RatFunc R) C / D := by
    simpa [x, D] using hC
  have hb_scaled :
      b * D ^ 2 = algebraMap (Polynomial R) (RatFunc R) (B * d) := by
    calc
      b * D ^ 2 =
          (algebraMap (Polynomial R) (RatFunc R) B / D) * D ^ 2 := by
            rw [hb_rep]
      _ = algebraMap (Polynomial R) (RatFunc R) B * D := by
            field_simp [hD]
      _ = algebraMap (Polynomial R) (RatFunc R) (B * d) := by
            simp [D, map_mul]
  have hc_scaled :
      c * D ^ 2 = algebraMap (Polynomial R) (RatFunc R) (C * d) := by
    calc
      c * D ^ 2 =
          (algebraMap (Polynomial R) (RatFunc R) C / D) * D ^ 2 := by
            rw [hc_rep]
      _ = algebraMap (Polynomial R) (RatFunc R) C * D := by
            field_simp [hD]
      _ = algebraMap (Polynomial R) (RatFunc R) (C * d) := by
            simp [D, map_mul]
  have hobs :
      NormalizedSignObstructionFree.{u, v} b c :=
    (normalizedSignObstructionFree_iff_locallyIsotropic b c).mpr hlocal
  have hobs_scaled :
      NormalizedSignObstructionFree.{u, v} (b * D ^ 2) (c * D ^ 2) :=
    (normalizedSignObstructionFree_mul_square (R := R)
      (b := b) (c := c) (u := D) (v := D) hD hD).mpr hobs
  have hobs_poly :
      NormalizedSignObstructionFree.{u, v}
        (algebraMap (Polynomial R) (RatFunc R) (B * d))
        (algebraMap (Polynomial R) (RatFunc R) (C * d)) := by
    intro K _ _ _ _ _
    have hs := hobs_scaled (K := K)
    simpa [hb_scaled, hc_scaled] using hs
  have hglobal_poly :
      Diagonal.TernaryIsotropic 1
        (algebraMap (Polynomial R) (RatFunc R) (B * d))
        (algebraMap (Polynomial R) (RatFunc R) (C * d)) :=
    hpoly (B * d) (C * d) hobs_poly
  have hglobal_scaled :
      Diagonal.TernaryIsotropic 1 (b * D ^ 2) (c * D ^ 2) := by
    simpa [hb_scaled, hc_scaled] using hglobal_poly
  exact
    (Diagonal.ternary_isotropic_mul_square (F := RatFunc R)
      (a₀ := 1) (a₁ := b) (a₂ := c)
      (u₀ := 1) (u₁ := D) (u₂ := D)
      one_ne_zero hD hD).mp (by simpa using hglobal_scaled)

private theorem normalizedTernaryLocalGlobal_of_regular_polynomial
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hreg : RegularPolynomialNormalizedTernaryLocalGlobal.{u, v} R) :
    NormalizedTernaryLocalGlobal.{u, v} R :=
  normalizedTernaryLocalGlobal_of_polynomial R
    (polynomialNormalizedTernaryLocalGlobal_of_regular R hreg)

private theorem normalizedTernaryLocalGlobal_iff_regular_polynomial_coefficients
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    NormalizedTernaryLocalGlobal.{u, v} R ↔
      RegularPolynomialNormalizedTernaryLocalGlobal.{u, v} R := by
  constructor
  · intro hnorm
    exact regularPolynomialNormalizedTernaryLocalGlobal_of_polynomial R
      (polynomialNormalizedTernaryLocalGlobal_of_normalized R hnorm)
  · exact normalizedTernaryLocalGlobal_of_regular_polynomial R

private theorem regularPolynomialNormalizedTernaryLocalGlobal_iff_binary_polynomial_or_square_right
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    RegularPolynomialNormalizedTernaryLocalGlobal.{u, v} R ↔
      ∀ B C : Polynomial R,
        B ≠ 0 →
          C ≠ 0 →
            NormalizedSignObstructionFree.{u, v}
              (algebraMap (Polynomial R) (RatFunc R) B)
              (algebraMap (Polynomial R) (RatFunc R) C) →
            (∃ p q d : Polynomial R,
              d ≠ 0 ∧
                (algebraMap (Polynomial R) (RatFunc R) p) ^ 2 +
                  algebraMap (Polynomial R) (RatFunc R) C *
                    (algebraMap (Polynomial R) (RatFunc R) q) ^ 2 =
                  (-(algebraMap (Polynomial R) (RatFunc R) B)) *
                    (algebraMap (Polynomial R) (RatFunc R) d) ^ 2) ∨
              IsSquare (-(algebraMap (Polynomial R) (RatFunc R) C)) := by
  constructor
  · intro hreg B C hB hC hobs
    have hglobal := hreg B C hB hC hobs
    rcases (Diagonal.ternary_isotropic_one_iff_binary_or_isSquare_neg_right).mp
        hglobal with hbin | hsquare
    · left
      exact binary_representation_iff_exists_polynomial_solution.mp hbin
    · right
      exact hsquare
  · intro h B C hB hC hobs
    apply (Diagonal.ternary_isotropic_one_iff_binary_or_isSquare_neg_right).mpr
    rcases h B C hB hC hobs with hpoly | hsquare
    · left
      exact binary_representation_iff_exists_polynomial_solution.mpr hpoly
    · right
      exact hsquare

private theorem regularPolynomialNormalizedTernaryLocalGlobal_iff_clearedBinary_right
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    RegularPolynomialNormalizedTernaryLocalGlobal.{u, v} R ↔
      ∀ B C : Polynomial R,
        B ≠ 0 →
          C ≠ 0 →
            NormalizedSignObstructionFree.{u, v}
              (algebraMap (Polynomial R) (RatFunc R) B)
              (algebraMap (Polynomial R) (RatFunc R) C) →
            ClearedBinaryOrSquareRight R B C := by
  simpa [ClearedBinaryOrSquareRight] using
    (regularPolynomialNormalizedTernaryLocalGlobal_iff_binary_polynomial_or_square_right
      (R := R))

private theorem regularPolynomialNormalizedTernaryLocalGlobal_iff_clearedBinaryConstruction_right
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    RegularPolynomialNormalizedTernaryLocalGlobal.{u, v} R ↔
      ClearedBinaryConstructionRight.{u, v} R := by
  simpa [ClearedBinaryConstructionRight] using
    (regularPolynomialNormalizedTernaryLocalGlobal_iff_clearedBinary_right
      (R := R))

private theorem normalizedTernaryLocalGlobal_iff_clearedBinaryConstruction_right
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    NormalizedTernaryLocalGlobal.{u, v} R ↔
      ClearedBinaryConstructionRight.{u, v} R := by
  calc
    NormalizedTernaryLocalGlobal.{u, v} R ↔
        RegularPolynomialNormalizedTernaryLocalGlobal.{u, v} R :=
      normalizedTernaryLocalGlobal_iff_regular_polynomial_coefficients R
    _ ↔ ClearedBinaryConstructionRight.{u, v} R :=
      regularPolynomialNormalizedTernaryLocalGlobal_iff_clearedBinaryConstruction_right R

private theorem normalizedTernaryLocalGlobal_iff_clearedBinaryConstructionNoObstruction_right
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    NormalizedTernaryLocalGlobal.{u, v} R ↔
      ClearedBinaryConstructionRightNoObstruction.{u, v} R := by
  calc
    NormalizedTernaryLocalGlobal.{u, v} R ↔
        ClearedBinaryConstructionRight.{u, v} R :=
      normalizedTernaryLocalGlobal_iff_clearedBinaryConstruction_right R
    _ ↔ ClearedBinaryConstructionRightNoObstruction.{u, v} R :=
      clearedBinaryConstructionRight_iff_noObstruction R

private theorem normalizedTernaryLocalGlobal_iff_squarefree_clearedBinary_right
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    NormalizedTernaryLocalGlobal.{u, v} R ↔
      SquarefreeClearedBinaryConstructionRightNoObstruction.{u, v} R := by
  calc
    NormalizedTernaryLocalGlobal.{u, v} R ↔
        ClearedBinaryConstructionRightNoObstruction.{u, v} R :=
      normalizedTernaryLocalGlobal_iff_clearedBinaryConstructionNoObstruction_right R
    _ ↔ SquarefreeClearedBinaryConstructionRightNoObstruction.{u, v} R :=
      clearedBinaryConstructionRightNoObstruction_iff_squarefree R

private theorem normalizedTernaryLocalGlobal_iff_squarefree_binary_right
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    NormalizedTernaryLocalGlobal.{u, v} R ↔
      SquarefreeBinaryConstructionRightNoObstruction.{u, v} R := by
  calc
    NormalizedTernaryLocalGlobal.{u, v} R ↔
        SquarefreeClearedBinaryConstructionRightNoObstruction.{u, v} R :=
      normalizedTernaryLocalGlobal_iff_squarefree_clearedBinary_right R
    _ ↔ SquarefreeBinaryConstructionRightNoObstruction.{u, v} R :=
      squarefreeClearedBinaryConstructionRightNoObstruction_iff_binary R

theorem normalizedTernaryLocalGlobal_iff_squarefree_nonterminal_right
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    NormalizedTernaryLocalGlobal.{u, v} R ↔
      SquarefreeNonterminalBinaryConstructionRightNoObstruction.{u, v} R := by
  calc
    NormalizedTernaryLocalGlobal.{u, v} R ↔
        SquarefreeBinaryConstructionRightNoObstruction.{u, v} R :=
      normalizedTernaryLocalGlobal_iff_squarefree_binary_right R
    _ ↔ SquarefreeNonterminalBinaryConstructionRightNoObstruction.{u, v} R :=
      squarefreeBinaryConstructionRightNoObstruction_iff_nonterminal R

end RatFunc

end RatFuncWittLocalGlobal
