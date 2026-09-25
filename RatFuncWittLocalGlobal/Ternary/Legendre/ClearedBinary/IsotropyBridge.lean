/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Ternary.Legendre.ClearedBinary.LocalConditions

/-!
# Cleared-binary isotropy bridge
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

theorem clearedBinaryOrSquareRight_iff_binary_or_square
    {R : Type u} [Field R] (B C : Polynomial R) :
    ClearedBinaryOrSquareRight R B C ↔
      ClearedBinaryRight R B C ∨
        IsSquare (-(algebraMap (Polynomial R) (RatFunc R) C)) := by
  rfl

/--
Turn the ternary Legendre identity after removing the common factor
`B = G * B₁`, `C = G * C₁` into the right-oriented cleared binary identity.
-/
theorem clearedBinaryRight_of_gcd_legendre_identity
    {R : Type u} [Field R]
    {G B₁ C₁ B C r q d : Polynomial R}
    (hB : B = G * B₁) (hC : C = G * C₁) (hd : d ≠ 0)
    (h : G * r ^ 2 + C₁ * q ^ 2 + B₁ * d ^ 2 = 0) :
    ClearedBinaryRight R B C := by
  have hpoly : (G * r) ^ 2 + (G * C₁) * q ^ 2 = -(G * B₁) * d ^ 2 := by
    have hsum : G * r ^ 2 + C₁ * q ^ 2 = -(B₁ * d ^ 2) := by
      exact add_eq_zero_iff_eq_neg.mp h
    calc
      (G * r) ^ 2 + (G * C₁) * q ^ 2
          = G * (G * r ^ 2 + C₁ * q ^ 2) := by
            rw [pow_two, pow_two, pow_two]
            rw [mul_add]
            congr 1
            · ac_rfl
            · ac_rfl
      _ = G * (-(B₁ * d ^ 2)) := by rw [hsum]
      _ = -(G * (B₁ * d ^ 2)) := by rw [mul_neg]
      _ = -(G * B₁) * d ^ 2 := by
            rw [neg_mul]
            congr 1
            rw [mul_assoc]
  refine ⟨G * r, q, d, hd, ?_⟩
  rw [hB, hC]
  simpa [map_add, map_mul, map_pow, map_neg] using
    congrArg (algebraMap (Polynomial R) (RatFunc R)) hpoly

theorem legendre_identity_q_ne_zero_of_d_eq_zero_of_nonzero
    {R : Type u} [Field R]
    {G B₁ C₁ r q d : Polynomial R}
    (hG : G ≠ 0) (hne : r ≠ 0 ∨ q ≠ 0 ∨ d ≠ 0)
    (h : G * r ^ 2 + C₁ * q ^ 2 + B₁ * d ^ 2 = 0) (hd0 : d = 0) :
    q ≠ 0 := by
  intro hq0
  have hr0 : r = 0 := by
    have hGr : G * r ^ 2 = 0 := by
      simpa [hq0, hd0] using h
    have hr2 : r ^ 2 = 0 := (mul_eq_zero.mp hGr).resolve_left hG
    exact eq_zero_of_pow_eq_zero hr2
  rcases hne with hr | hq | hd
  · exact hr hr0
  · exact hq hq0
  · exact hd hd0

theorem isSquare_neg_right_of_gcd_legendre_identity_d_eq_zero
    {R : Type u} [Field R]
    {G B₁ C₁ C r q d : Polynomial R}
    (hC : C = G * C₁) (hq : q ≠ 0)
    (h : G * r ^ 2 + C₁ * q ^ 2 + B₁ * d ^ 2 = 0) (hd0 : d = 0) :
    IsSquare (-(algebraMap (Polynomial R) (RatFunc R) C)) := by
  let φ := algebraMap (Polynomial R) (RatFunc R)
  have hsum : G * r ^ 2 + C₁ * q ^ 2 = 0 := by
    simpa [hd0] using h
  have hpoly : (G * r) ^ 2 + (G * C₁) * q ^ 2 = 0 := by
    calc
      (G * r) ^ 2 + (G * C₁) * q ^ 2
          = G * (G * r ^ 2 + C₁ * q ^ 2) := by
            rw [pow_two, pow_two, pow_two]
            rw [mul_add]
            congr 1
            · ac_rfl
            · ac_rfl
      _ = 0 := by rw [hsum, mul_zero]
  refine ⟨φ (G * r) / φ q, ?_⟩
  have hqmap : φ q ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hq
  rw [hC]
  have hmap := congrArg φ hpoly
  have hzero : (φ (G * r)) ^ 2 + φ (G * C₁) * (φ q) ^ 2 = 0 := by
    simpa [φ, map_add, map_mul, map_pow] using hmap
  apply (mul_right_injective₀ (pow_ne_zero 2 hqmap))
  calc
    (φ q) ^ 2 * (-(φ (G * C₁)))
        = (φ (G * r)) ^ 2 := by linear_combination -hzero
    _ = (φ q) ^ 2 * ((φ (G * r) / φ q) * (φ (G * r) / φ q)) := by
          field_simp [hqmap]

theorem clearedBinaryRight_of_gcd_legendre_identity_of_not_isSquare_neg_right
    {R : Type u} [Field R]
    {G B₁ C₁ B C r q d : Polynomial R}
    (hB : B = G * B₁) (hC : C = G * C₁) (hG : G ≠ 0)
    (hne : r ≠ 0 ∨ q ≠ 0 ∨ d ≠ 0)
    (hnotC : ¬ IsSquare (-(algebraMap (Polynomial R) (RatFunc R) C)))
    (h : G * r ^ 2 + C₁ * q ^ 2 + B₁ * d ^ 2 = 0) :
    ClearedBinaryRight R B C := by
  by_cases hd : d = 0
  · have hq : q ≠ 0 :=
      legendre_identity_q_ne_zero_of_d_eq_zero_of_nonzero hG hne h hd
    exact False.elim (hnotC (isSquare_neg_right_of_gcd_legendre_identity_d_eq_zero hC hq h hd))
  · exact clearedBinaryRight_of_gcd_legendre_identity hB hC hd h

theorem clearedBinaryRight_of_squarefreeGcdSplit_legendre_identity_of_not_isSquare_neg_right
    {R : Type u} [Field R] {B C r q d : Polynomial R}
    (s : SquarefreeGcdSplit B C) (hne : r ≠ 0 ∨ q ≠ 0 ∨ d ≠ 0)
    (hnotC : ¬ IsSquare (-(algebraMap (Polynomial R) (RatFunc R) C)))
    (h : s.G * r ^ 2 + s.C₁ * q ^ 2 + s.B₁ * d ^ 2 = 0) :
    ClearedBinaryRight R B C :=
  clearedBinaryRight_of_gcd_legendre_identity_of_not_isSquare_neg_right
    s.hB s.hC s.G_ne_zero hne hnotC h

theorem clearedBinaryConstructionRight_iff_noObstruction
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    ClearedBinaryConstructionRight.{u, v} R ↔
      ClearedBinaryConstructionRightNoObstruction.{u, v} R := by
  constructor
  · intro h B C hB hC hno
    exact h B C hB hC
      ((normalizedSignObstructionFree_iff_not_hasObstruction _ _).mpr hno)
  · intro h B C hB hC hfree
    exact h B C hB hC
      ((normalizedSignObstructionFree_iff_not_hasObstruction _ _).mp hfree)

theorem squarefreeNonterminalBinaryConstructionRightNoOrderingObstruction_of_gcdLegendre
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (h :
      SquarefreeGcdLegendreConstructionNoOrderingObstruction R) :
    SquarefreeNonterminalBinaryConstructionRightNoOrderingObstruction R := by
  intro B C hB hC hBsq hCsq hno hnotB hnotC
  rcases h B C hB hC hBsq hCsq hno hnotB hnotC with
    ⟨s, r, q, d, hne, hidentity⟩
  exact clearedBinaryRight_of_squarefreeGcdSplit_legendre_identity_of_not_isSquare_neg_right
    s hne hnotC hidentity

theorem squarefreeClearedBinaryConstructionRightNoObstruction_iff_binary
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    SquarefreeClearedBinaryConstructionRightNoObstruction.{u, v} R ↔
      SquarefreeBinaryConstructionRightNoObstruction.{u, v} R := by
  constructor
  · intro h B C hB hC hBsq hCsq hno hnot_square
    rcases (clearedBinaryOrSquareRight_iff_binary_or_square B C).mp
        (h B C hB hC hBsq hCsq hno) with hbinary | hsquare
    · exact hbinary
    · exact False.elim (hnot_square hsquare)
  · intro h B C hB hC hBsq hCsq hno
    by_cases hsquare : IsSquare (-(algebraMap (Polynomial R) (RatFunc R) C))
    · exact (clearedBinaryOrSquareRight_iff_binary_or_square B C).mpr (Or.inr hsquare)
    · exact (clearedBinaryOrSquareRight_iff_binary_or_square B C).mpr
        (Or.inl (h B C hB hC hBsq hCsq hno hsquare))

theorem clearedBinaryOrSquareRight_iff_ternary_isotropic
    {R : Type u} [Field R] (B C : Polynomial R) :
    ClearedBinaryOrSquareRight R B C ↔
      Diagonal.TernaryIsotropic 1
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C) := by
  constructor
  · intro h
    apply (Diagonal.ternary_isotropic_one_iff_binary_or_isSquare_neg_right).mpr
    rcases h with hpoly | hsquare
    · left
      exact binary_representation_iff_exists_polynomial_solution.mpr hpoly
    · right
      exact hsquare
  · intro h
    rcases (Diagonal.ternary_isotropic_one_iff_binary_or_isSquare_neg_right).mp h with
      hbin | hsquare
    · left
      exact binary_representation_iff_exists_polynomial_solution.mp hbin
    · right
      exact hsquare

end RatFunc
end RatFuncWittLocalGlobal
