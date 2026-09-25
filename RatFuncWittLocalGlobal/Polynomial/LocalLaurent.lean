/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Polynomial.LaurentPoint

/-!
# Algebra of local Laurent leading coefficients

Dimension-independent rules for multiplication, negation, ordinary non-root
values, and normalized linear factors.
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u

noncomputable section

/-- The leading coefficient after substituting the local Laurent parameter
at a real center into a polynomial. -/
def localLaurentLeadingCoeff
    {R : Type u} [Field R] (r ε : R) (p : Polynomial R) : R :=
  (algebraMap (Polynomial R) (LaurentSeries R)
    (p.comp (C ε * X + C r))).leadingCoeff

/-- Local Laurent leading coefficients are multiplicative. -/
theorem localLaurentLeadingCoeff_mul
    {R : Type u} [Field R]
    (r ε : R) (p q : Polynomial R) :
    localLaurentLeadingCoeff r ε (p * q) =
      localLaurentLeadingCoeff r ε p *
        localLaurentLeadingCoeff r ε q := by
  simp [localLaurentLeadingCoeff, HahnSeries.leadingCoeff_mul]

/-- At a point where a polynomial does not vanish, the local Laurent leading
coefficient is its ordinary value. -/
theorem localLaurentLeadingCoeff_eq_eval_of_ne_zero
    {R : Type u} [Field R]
    {r ε : R} {p : Polynomial R} (hp : p.eval r ≠ 0) :
    localLaurentLeadingCoeff r ε p = p.eval r := by
  exact RatFunc.scaledShiftedPolynomial_laurentSeries_leadingCoeff hp

/-- The normalized linear factor has local Laurent leading coefficient equal
to the orientation scalar. -/
theorem localLaurentLeadingCoeff_X_sub_C
    {R : Type u} [Field R] (r ε : R) :
    localLaurentLeadingCoeff r ε (X - C r) = ε := by
  unfold localLaurentLeadingCoeff
  rw [show ((X - C r : Polynomial R).comp (C ε * X + C r)) = C ε * X by
    simp [Polynomial.sub_comp]]
  exact RatFunc.powerSeries_C_mul_X_laurentSeries_leadingCoeff ε

end

end RatFuncWittLocalGlobal
