/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Ordering.Obstruction

/-!
# Statements used by the normalized ternary reduction

This file contains only the propositions transported through the ternary
reduction.  Polynomial normalization and cleared-binary constructions live in
later modules, so consumers of these statements do not inherit those
implementations.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

def NormalizedTernaryLocalGlobal
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] : Prop :=
  ∀ b c : RatFunc R,
    TernaryLocallyIsotropic.{u, v} 1 b c →
      Diagonal.TernaryIsotropic 1 b c

/-- The README-shaped regular ternary local-global statement. -/
def TernaryLocalGlobal
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] : Prop :=
  ∀ a₀ a₁ a₂ : RatFunc R,
    a₀ ≠ 0 ∧ a₁ ≠ 0 ∧ a₂ ≠ 0 →
      (∀ {K : Type v}
        [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
        [Algebra (RatFunc R) K],
        ∃ x₀ x₁ x₂ : K,
          (x₀, x₁, x₂) ≠ (0, 0, 0) ∧
            algebraMap (RatFunc R) K a₀ * x₀ ^ 2 +
            algebraMap (RatFunc R) K a₁ * x₁ ^ 2 +
            algebraMap (RatFunc R) K a₂ * x₂ ^ 2 = 0) →
      ∃ x₀ x₁ x₂ : RatFunc R,
        (x₀, x₁, x₂) ≠ (0, 0, 0) ∧
          a₀ * x₀ ^ 2 + a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2 = 0

end RatFunc

end RatFuncWittLocalGlobal
