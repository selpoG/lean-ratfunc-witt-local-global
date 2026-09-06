/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Ternary.Quaternion.Criterion.RealSplit

/-!
# Residue predicates for the rational function field

Only the two residue bundles consumed by the maintained polynomial
Legendre/quaternion route live here.  General alternative place criteria are
preserved on the research branch rather than the public proof spine.
-/

namespace RatFuncWittLocalGlobal

universe u

variable {R : Type u}

/-- Finite residue triviality for quaternion symbols over `RatFunc R`. -/
def RatFuncQuaternionFiniteResiduesTrivialFor [Field R]
    (FiniteResidueTrivial : RatFunc R → RatFunc R → Polynomial R → Prop)
    (p q : RatFunc R) : Prop :=
  ∀ π : Polynomial R, Irreducible π → FiniteResidueTrivial p q π

/--
Residue triviality assembled from the finite-place bundle and an
infinity-place predicate.
-/
def RatFuncQuaternionResiduesTrivialFor [Field R]
    (FiniteResidueTrivial : RatFunc R → RatFunc R → Polynomial R → Prop)
    (InfinityResidueTrivial : RatFunc R → RatFunc R → Prop)
    (p q : RatFunc R) : Prop :=
  RatFuncQuaternionFiniteResiduesTrivialFor FiniteResidueTrivial p q ∧
    InfinityResidueTrivial p q

end RatFuncWittLocalGlobal
