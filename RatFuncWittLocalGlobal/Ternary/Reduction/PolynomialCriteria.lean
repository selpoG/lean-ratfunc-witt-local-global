/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Ternary.Reduction.PolynomialNormalization

/-!
# Polynomial criteria for normalized ternary local-global
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

theorem normalizedTernaryLocalGlobal_of_squarefree_nonterminal_right
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (h : SquarefreeNonterminalBinaryConstructionRightNoObstruction.{u, v} R) :
    NormalizedTernaryLocalGlobal.{u, v} R :=
  (normalizedTernaryLocalGlobal_iff_squarefree_nonterminal_right R).mpr h

theorem normalizedTernaryLocalGlobal_of_polynomialLegendre_of_factorMod_of_orderingRealization
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hreal : NormalizedOrderingRealization.{u, v} R)
    (hlegendre : PolynomialLegendreConstruction R)
    (hfactor : SquarefreeGcdLegendreFactorModConditionsNoOrderingObstruction R) :
    NormalizedTernaryLocalGlobal.{u, v} R :=
  normalizedTernaryLocalGlobal_of_squarefree_nonterminal_right R
    (squarefreeNonterminalBinaryConstructionRightNoObstruction_of_noOrdering
      hreal
      (squarefreeNonterminalBinaryConstructionRightNoOrderingObstruction_of_gcdLegendre R
      (squarefreeGcdLegendreConstructionNoOrderingObstruction_of_polynomialLegendre_of_factorMod
          hlegendre hfactor)))

theorem normalizedTernaryLocalGlobal_of_polynomialLegendre_of_splitDivisors_of_orderingRealization
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hreal : NormalizedOrderingRealization.{u, v} R)
    (hlegendre : PolynomialLegendreConstruction R)
    (hsplit :
      SquarefreeGcdLegendreLinearAndNonlinearDivisorConditionsNoOrderingObstruction R) :
    NormalizedTernaryLocalGlobal.{u, v} R :=
  normalizedTernaryLocalGlobal_of_polynomialLegendre_of_factorMod_of_orderingRealization
    R hreal hlegendre
    (squarefreeGcdLegendreFactorModConditionsNoOrderingObstruction_of_splitDivisors
      hsplit)

theorem normalizedTernaryLocalGlobal_of_polynomialLegendre_of_linearSigns_of_orderingRealization
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hreal : NormalizedOrderingRealization.{u, v} R)
    (hlegendre : PolynomialLegendreConstruction R)
    (hlinear : SquarefreeGcdLegendreLinearDivisorSignConditionsNoOrderingObstruction R)
    (hnonlinear : NonlinearIrreducibleDivisorSquareMod R) :
    NormalizedTernaryLocalGlobal.{u, v} R :=
  normalizedTernaryLocalGlobal_of_polynomialLegendre_of_splitDivisors_of_orderingRealization
    R hreal hlegendre
    (linearAndNonlinearDivisorConditionsNoOrderingObstruction_of_linearSigns
      hlinear hnonlinear)

theorem normalizedTernaryLocalGlobal_of_polynomialLegendre_of_rootObstructions
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hreal : NormalizedOrderingRealization.{u, v} R)
    (hlegendre : PolynomialLegendreConstruction R)
    (hroot : SquarefreeGcdLegendreLinearRootObstructionPrinciples R)
    (hnonlinear : NonlinearIrreducibleDivisorSquareMod R) :
    NormalizedTernaryLocalGlobal.{u, v} R :=
  normalizedTernaryLocalGlobal_of_polynomialLegendre_of_linearSigns_of_orderingRealization
    R hreal hlegendre
    (linearDivisorSignConditionsNoOrderingObstruction_of_rootObstructionPrinciples hroot)
    hnonlinear

theorem normalizedTernaryLocalGlobal_of_polynomialLegendre_of_rootOrderedPos
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hreal : NormalizedOrderingRealization.{u, v} R)
    (hlegendre : PolynomialLegendreConstruction R)
    (hordered : SquarefreeGcdLegendreLinearRootOrderedPosPrinciples R)
    (hnonlinear : NonlinearIrreducibleDivisorSquareMod R) :
    NormalizedTernaryLocalGlobal.{u, v} R :=
  normalizedTernaryLocalGlobal_of_polynomialLegendre_of_rootObstructions
    R hreal hlegendre
    (linearRootObstructionPrinciples_of_orderedPosPrinciples hordered)
    hnonlinear

theorem ternary_isotropic_of_locally_isotropic_of_normalized
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hnorm : NormalizedTernaryLocalGlobal.{u, v} R)
    {a₀ a₁ a₂ : RatFunc R}
    (ha₀ : a₀ ≠ 0)
    (hlocal : TernaryLocallyIsotropic.{u, v} a₀ a₁ a₂) :
    Diagonal.TernaryIsotropic a₀ a₁ a₂ := by
  have hlocal_norm :
      TernaryLocallyIsotropic.{u, v} 1 (a₁ / a₀) (a₂ / a₀) :=
    (ternary_locally_isotropic_normalize_first (R := R)
      (a₀ := a₀) (a₁ := a₁) (a₂ := a₂) ha₀).mpr hlocal
  have hglobal_norm :
      Diagonal.TernaryIsotropic 1 (a₁ / a₀) (a₂ / a₀) :=
    hnorm (a₁ / a₀) (a₂ / a₀) hlocal_norm
  exact (Diagonal.ternary_isotropic_normalize_first ha₀).mp hglobal_norm

theorem ternary_isotropic_of_locally_isotropic_of_normalized_of_regular
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hnorm : NormalizedTernaryLocalGlobal.{u, v} R)
    {a₀ a₁ a₂ : RatFunc R}
    (hreg : a₀ ≠ 0 ∧ a₁ ≠ 0 ∧ a₂ ≠ 0)
    (hlocal : TernaryLocallyIsotropic.{u, v} a₀ a₁ a₂) :
    Diagonal.TernaryIsotropic a₀ a₁ a₂ :=
  ternary_isotropic_of_locally_isotropic_of_normalized hnorm hreg.1 hlocal

theorem ternary_tuple_isotropic_of_forall_realClosedExtension_of_normalized
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hnorm : NormalizedTernaryLocalGlobal.{u, v} R)
    (a₀ a₁ a₂ : RatFunc R)
    (hreg : a₀ ≠ 0 ∧ a₁ ≠ 0 ∧ a₂ ≠ 0)
    (hlocal :
      ∀ {K : Type v}
        [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
        [Algebra (RatFunc R) K],
        ∃ x₀ x₁ x₂ : K,
          (x₀, x₁, x₂) ≠ (0, 0, 0) ∧
            algebraMap (RatFunc R) K a₀ * x₀ ^ 2 +
            algebraMap (RatFunc R) K a₁ * x₁ ^ 2 +
            algebraMap (RatFunc R) K a₂ * x₂ ^ 2 = 0) :
    ∃ x₀ x₁ x₂ : RatFunc R,
      (x₀, x₁, x₂) ≠ (0, 0, 0) ∧
        a₀ * x₀ ^ 2 + a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2 = 0 := by
  have hlocal' : TernaryLocallyIsotropic.{u, v} a₀ a₁ a₂ := by
    intro K _ _ _ _ _
    rcases hlocal (K := K) with ⟨x₀, x₁, x₂, hx_ne, hx_sum⟩
    exact Diagonal.ternary_isotropic_iff_exists_tuple_ne.mpr
      ⟨x₀, x₁, x₂, hx_ne, hx_sum⟩
  have hglobal : Diagonal.TernaryIsotropic a₀ a₁ a₂ :=
    ternary_isotropic_of_locally_isotropic_of_normalized_of_regular hnorm hreg hlocal'
  exact Diagonal.ternary_isotropic_iff_exists_tuple_ne.mp hglobal

theorem ternaryLocalGlobal_of_normalized
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hnorm : NormalizedTernaryLocalGlobal.{u, v} R) :
    TernaryLocalGlobal.{u, v} R := by
  intro a₀ a₁ a₂ hreg hlocal
  exact ternary_tuple_isotropic_of_forall_realClosedExtension_of_normalized
    hnorm a₀ a₁ a₂ hreg hlocal

end RatFunc
end RatFuncWittLocalGlobal
