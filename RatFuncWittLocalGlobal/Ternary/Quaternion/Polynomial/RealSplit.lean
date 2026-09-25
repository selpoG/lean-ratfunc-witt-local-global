/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Ternary.Quaternion.Polynomial.Criteria

/-!
# Real-split transport for polynomial symbols

This module contains the real-split bridge used by the public ternary proof.
-/

namespace RatFuncWittLocalGlobal

universe u v

variable {R : Type u}

/-- Predicate-form version using `RatFunc.TernaryLocallyIsotropic`. -/
theorem ratFuncQuaternionRealSplit_iff_ternaryLocallyIsotropic_normalize_first
    [Field R] {a₀ a₁ a₂ : RatFunc R} (ha₀ : a₀ ≠ 0) :
    RatFuncQuaternionRealSplit.{u, v} (-(a₁ / a₀)) (-(a₂ / a₀)) ↔
      RatFunc.TernaryLocallyIsotropic.{u, v} a₀ a₁ a₂ :=
  ratFuncQuaternionRealSplit_iff_forall_ternary_isotropic_normalize_first ha₀

/--
For a polynomial ternary form, absence of a common strict sign supplies the
real-split input for the normalized polynomial quaternion symbol.
-/
theorem polynomialTernaryQuaternionRealSplit_of_not_sameStrictSign
    [Field R] {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hno :
      ¬ RatFunc.SameStrictSignOrdering
        (algebraMap (Polynomial R) (RatFunc R) A)
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C)) :
    RatFuncQuaternionRealSplit.{u, v}
      (polynomialTernaryQuaternionCoeff A B)
      (polynomialTernaryQuaternionCoeff A C) := by
  have hAφ : algebraMap (Polynomial R) (RatFunc R) A ≠ 0 :=
    _root_.RatFunc.algebraMap_ne_zero hA0
  have hBφ : algebraMap (Polynomial R) (RatFunc R) B ≠ 0 :=
    _root_.RatFunc.algebraMap_ne_zero hB0
  have hCφ : algebraMap (Polynomial R) (RatFunc R) C ≠ 0 :=
    _root_.RatFunc.algebraMap_ne_zero hC0
  have hlocal :
      RatFunc.TernaryLocallyIsotropic.{u, v}
        (algebraMap (Polynomial R) (RatFunc R) A)
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C) :=
    RatFunc.ternaryLocallyIsotropic_of_not_sameStrictSignOrdering hAφ hBφ hCφ hno
  have hreal :
      RatFuncQuaternionRealSplit.{u, v}
        (-(algebraMap (Polynomial R) (RatFunc R) B /
            algebraMap (Polynomial R) (RatFunc R) A))
        (-(algebraMap (Polynomial R) (RatFunc R) C /
            algebraMap (Polynomial R) (RatFunc R) A)) :=
    (ratFuncQuaternionRealSplit_iff_ternaryLocallyIsotropic_normalize_first
      hAφ).mpr hlocal
  change
    RatFuncQuaternionRealSplit.{u, v}
      (-(algebraMap (Polynomial R) (RatFunc R) B /
          algebraMap (Polynomial R) (RatFunc R) A))
      (-(algebraMap (Polynomial R) (RatFunc R) C /
          algebraMap (Polynomial R) (RatFunc R) A))
  exact hreal

end RatFuncWittLocalGlobal
