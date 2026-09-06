/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Core.RealClosedDiagonal

/-!
# Strict signs of finite scalar families

This module contains the dimension-independent sign predicate used by the
finite-dimensional compression arguments and its real-closed isotropy
consumer.
-/

namespace RatFuncWittLocalGlobal

universe u

/-- A scalar family is strictly positive everywhere or strictly negative
everywhere. -/
def ScalarFamilySameStrictSign
    {F : Type u} [LinearOrder F] [Zero F]
    {ι : Type*} (A : ι → F) : Prop :=
  (∀ i, 0 < A i) ∨ (∀ i, A i < 0)

/-- Over a real-closed field, a regular scalar family with no common strict
sign is isotropic. -/
theorem Diagonal.isotropic_of_not_scalarFamilySameStrictSign
    {K ι : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [IsRealClosed K] [Fintype ι] [Nonempty ι]
    (A : ι → K) (hA : ∀ i, A i ≠ 0)
    (hno : ¬ ScalarFamilySameStrictSign A) :
    Diagonal.Isotropic A := by
  by_contra haniso
  exact hno ((Diagonal.not_isotropic_iff_all_pos_or_all_neg hA).mp haniso)

end RatFuncWittLocalGlobal
