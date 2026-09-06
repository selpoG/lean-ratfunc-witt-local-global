/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.RealClosure.Final
import RatFuncWittLocalGlobal.Ternary.NormalizedLocalGlobal

/-!
# Ordered-real-closure endpoint for ternary local-global

`OrderedRealClosure.normalizedOrderingRealization_of_maximal_orderedIntermediate`
supplies the only real-place input used by the normalized quaternion endpoint.
This file consumes that construction at the endpoint, leaving no separate
real-closure or polynomial-Legendre hypotheses in the resulting theorem.
-/

namespace RatFuncWittLocalGlobal

universe u

variable {R : Type u}

/--
The ternary local-global principle after discharging the normalized ordering
realization by the maximal ordered-intermediate construction.

The displayed typeclass assumptions are the ambient assumptions already built
into `RatFunc.TernaryLocalGlobal`; no additional real-closure, Legendre, or
linear-root input is required.
-/
theorem ternaryLocalGlobal_of_maximal_orderedIntermediate
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    RatFunc.TernaryLocalGlobal.{u, u} R :=
  ternaryLocalGlobal_of_normalizedOrderingRealization
    (OrderedRealClosure.normalizedOrderingRealization_of_maximal_orderedIntermediate
      (R := R))

namespace RatFunc

/--
README-shaped direct ternary wrapper in the same universe as the base field.
The explicit suffix records that the local extensions `K` are restricted to
`Type u`, matching the universe of the unconditional
`RatFunc.TernaryLocalGlobal.{u, u}` endpoint above.
-/
theorem ternary_isotropic_of_forall_realClosedExtension_same_universe
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (a₀ a₁ a₂ : RatFunc R)
    (hreg : a₀ ≠ 0 ∧ a₁ ≠ 0 ∧ a₂ ≠ 0)
    (hlocal :
      ∀ {K : Type u}
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
  exact RatFuncWittLocalGlobal.ternaryLocalGlobal_of_maximal_orderedIntermediate
    a₀ a₁ a₂ hreg hlocal

/--
The ternary isotropy predicate is equivalent to isotropy after every real
closed extension in the same universe.  The regularity hypothesis is needed
only for the local-to-global direction.
-/
theorem ternary_isotropic_iff_forall_realClosedExtension_same_universe
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (a₀ a₁ a₂ : RatFunc R)
    (hreg : a₀ ≠ 0 ∧ a₁ ≠ 0 ∧ a₂ ≠ 0) :
    Diagonal.TernaryIsotropic a₀ a₁ a₂ ↔
      ∀ {K : Type u}
        [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
        [Algebra (RatFunc R) K],
        Diagonal.TernaryIsotropic
          (algebraMap (RatFunc R) K a₀)
          (algebraMap (RatFunc R) K a₁)
          (algebraMap (RatFunc R) K a₂) := by
  constructor
  · intro h K _ _ _ _ _
    have hdiag :
        Diagonal.Isotropic (![a₀, a₁, a₂] : Fin 3 → RatFunc R) := by
      simpa using
        (Diagonal.isotropic_fin_three_iff
          (![a₀, a₁, a₂] : Fin 3 → RatFunc R)).mpr h
    have hdiagK :
        Diagonal.Isotropic
          (fun i : Fin 3 =>
            algebraMap (RatFunc R) K ((![a₀, a₁, a₂] : Fin 3 → RatFunc R) i)) :=
      Diagonal.isotropic_baseChange (K := K) hdiag
    have hternK :
        Diagonal.TernaryIsotropic
          (algebraMap (RatFunc R) K a₀)
          (algebraMap (RatFunc R) K a₁)
          (algebraMap (RatFunc R) K a₂) := by
      exact (Diagonal.isotropic_fin_three_iff
        (fun i : Fin 3 =>
          algebraMap (RatFunc R) K ((![a₀, a₁, a₂] : Fin 3 → RatFunc R) i))).mp hdiagK
    simpa using hternK
  · intro h
    apply Diagonal.ternary_isotropic_iff_exists_tuple_ne.mpr
    apply ternary_isotropic_of_forall_realClosedExtension_same_universe
      a₀ a₁ a₂ hreg
    intro K _ _ _ _ _
    exact Diagonal.ternary_isotropic_iff_exists_tuple_ne.mp (h (K := K))

end RatFunc

end RatFuncWittLocalGlobal
