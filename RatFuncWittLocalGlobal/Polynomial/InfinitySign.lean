/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Core.Basic

/-!
# Polynomial signs at infinity

Strict signs at the two real places at infinity, expressed through the leading
coefficient and degree parity.
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u

variable {R : Type u}

/-- A polynomial is strictly positive at positive infinity. -/
def PolynomialPosAtPosInfinity [LinearOrder R] [Semiring R]
    (P : Polynomial R) : Prop :=
  0 < P.leadingCoeff

/-- A polynomial is strictly negative at positive infinity. -/
def PolynomialNegAtPosInfinity [LinearOrder R] [Ring R]
    (P : Polynomial R) : Prop :=
  P.leadingCoeff < 0

/-- A polynomial is strictly positive at negative infinity. -/
def PolynomialPosAtNegInfinity [LinearOrder R] [Ring R]
    (P : Polynomial R) : Prop :=
  (Even P.natDegree ∧ 0 < P.leadingCoeff) ∨
    (Odd P.natDegree ∧ P.leadingCoeff < 0)

/-- A polynomial is strictly negative at negative infinity. -/
def PolynomialNegAtNegInfinity [LinearOrder R] [Ring R]
    (P : Polynomial R) : Prop :=
  (Even P.natDegree ∧ P.leadingCoeff < 0) ∨
    (Odd P.natDegree ∧ 0 < P.leadingCoeff)

end RatFuncWittLocalGlobal
