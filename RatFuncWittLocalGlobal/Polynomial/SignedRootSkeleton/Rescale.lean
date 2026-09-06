/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Polynomial.SignedRootSkeleton.Basic
import RatFuncWittLocalGlobal.Polynomial.LocalLaurent

/-!
# Rescaling a signed linear-root skeleton

The dimension-independent core of skeleton rescaling.  Multiplying the scale
by a nonzero scalar preserves the root set and multiplies both the polynomial
and every local Laurent leading coefficient by that scalar.
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u

noncomputable section

namespace SignedLinearRootSkeleton

variable {R : Type u} [Field R]

/-- Multiply the scale by one nonzero scalar without changing the roots. -/
def rescale (S : SignedLinearRootSkeleton R) (t : R) (ht : t ≠ 0) :
    SignedLinearRootSkeleton R where
  roots := S.roots
  scale := t * S.scale
  scale_ne_zero := mul_ne_zero ht S.scale_ne_zero

/-- Rescaling multiplies the represented polynomial by the same constant. -/
theorem poly_rescale (S : SignedLinearRootSkeleton R) (t : R) (ht : t ≠ 0) :
    (S.rescale t ht).poly = C t * S.poly := by
  change C (t * S.scale) * ∏ r ∈ S.roots, (X - C r) =
    C t * (C S.scale * ∏ r ∈ S.roots, (X - C r))
  rw [map_mul]
  ring

/-- Every local Laurent leading coefficient is multiplied by the rescaling
scalar. -/
@[simp]
theorem localLaurentLeadingCoeff_rescale
    (S : SignedLinearRootSkeleton R) (t : R) (ht : t ≠ 0)
    (r ε : R) :
    localLaurentLeadingCoeff r ε
        (S.rescale t ht).poly =
      t * localLaurentLeadingCoeff r ε S.poly := by
  rw [S.poly_rescale t ht, localLaurentLeadingCoeff_mul]
  simp [localLaurentLeadingCoeff]

end SignedLinearRootSkeleton

end

end RatFuncWittLocalGlobal
