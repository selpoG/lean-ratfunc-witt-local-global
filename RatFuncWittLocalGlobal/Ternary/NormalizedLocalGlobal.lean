/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Ternary.Reduction.PolynomialCriteria
import RatFuncWittLocalGlobal.Ternary.Quaternion.Polynomial.Endpoint

/-!
# Normalized ternary local-global theorem

This module closes the normalized polynomial Legendre argument from a
normalized ordering realization, then exposes the corresponding ternary
local-global statement.  It is the sole bridge needed by the public
ordered-real-closure endpoint.
-/

namespace RatFuncWittLocalGlobal

universe u

variable {R : Type u}

/-- The normalized polynomial Legendre argument from an ordering
realization. -/
theorem normalizedTernaryLocalGlobal_of_normalizedOrderingRealization
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, u} R) :
    RatFunc.NormalizedTernaryLocalGlobal.{u, u} R :=
  RatFunc.normalizedTernaryLocalGlobal_of_polynomialLegendre_of_rootOrderedPos
    R hrealization
    (polynomialLegendreConstruction_of_normalizedOrderingRealization hrealization)
    (RatFunc.squarefreeGcdLegendreLinearRootOrderedPosPrinciples_laurentSeries R)
    (RatFunc.nonlinearIrreducibleDivisorSquareMod_of_realClosed (R := R))

/-- The ternary local-global statement obtained from the normalized one. -/
theorem ternaryLocalGlobal_of_normalizedOrderingRealization
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, u} R) :
    RatFunc.TernaryLocalGlobal.{u, u} R :=
  RatFunc.ternaryLocalGlobal_of_normalized
    (normalizedTernaryLocalGlobal_of_normalizedOrderingRealization hrealization)

end RatFuncWittLocalGlobal
