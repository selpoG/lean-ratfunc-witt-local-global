/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.RealClosure.Intermediate
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# The quadratic algebra map into a simple adjoin

For a nonsquare `a` and a chosen square root `α` in the algebraic closure, the
quadratic algebra `QuadraticAlgebra E.carrier a 0` maps to the simple adjoin by
sending `ω` to `α`.  The linear-representation theorem from
`OrderedRealClosure` makes that map bijective.
-/

namespace RatFuncWittLocalGlobal
namespace OrderedRealClosure

universe u

open Polynomial
open Module

variable (F : Type u) [Field F] [LinearOrder F] [IsStrictOrderedRing F]

local notation "Ω" => AlgebraicClosure F

omit [IsStrictOrderedRing F] in
theorem quadraticAdjoinFact {E : Intermediate F} {a : E.carrier}
    (hnsq : ¬ IsSquare a) :
    Fact (∀ r : E.carrier, r ^ 2 ≠ a + 0 * r) := by
  refine ⟨?_⟩
  intro r hr
  apply hnsq
  exact ⟨r, by simpa [pow_two] using hr.symm⟩

theorem quadraticAdjoinAlgEquiv {E : Intermediate F} {a : E.carrier} {α : Ω}
    (hα : α ^ 2 = (a : Ω)) (hnsq : ¬ IsSquare a) :
    ∃ e : QuadraticAlgebra E.carrier a 0 ≃ₐ[E.carrier]
        IntermediateField.adjoin E.carrier ({α} : Set Ω),
      (e (QuadraticAlgebra.omega : QuadraticAlgebra E.carrier a 0) : Ω) = α := by
  let _ : Fact (∀ r : E.carrier, r ^ 2 ≠ a + 0 * r) :=
    quadraticAdjoinFact (F := F) hnsq
  let L := IntermediateField.adjoin E.carrier ({α} : Set Ω)
  let z : L := ⟨α, adjoin_mem_adjoinCarrier (F := F) E α⟩
  have hz : z * z = algebraMap E.carrier L a := by
    apply Subtype.ext
    change (α * α : Ω) = (a : Ω)
    simpa [pow_two] using hα
  let f : QuadraticAlgebra E.carrier a 0 →ₐ[E.carrier] L :=
    QuadraticAlgebra.lift ⟨z, by
      simpa [Algebra.smul_def] using hz⟩
  have hf_inj : Function.Injective f := by
    exact RingHom.injective f.toRingHom
  have hf_surj : Function.Surjective f := by
    intro w
    obtain ⟨x, y, hxy⟩ := exists_linear_representation (F := F) E hα hnsq w
    refine ⟨⟨x, y⟩, ?_⟩
    apply Subtype.ext
    rw [show f (⟨x, y⟩ : QuadraticAlgebra E.carrier a 0) =
        algebraMap E.carrier L x + y • z by
      simp [f, QuadraticAlgebra.lift_apply_apply, Algebra.smul_def]]
    change ((x : Ω) + (y : Ω) * α) = (w : Ω)
    exact hxy.symm
  let e : QuadraticAlgebra E.carrier a 0 ≃ₐ[E.carrier] L :=
    AlgEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨e, ?_⟩
  change ((e (QuadraticAlgebra.omega : QuadraticAlgebra E.carrier a 0) : L) : Ω) = α
  rw [show e (QuadraticAlgebra.omega : QuadraticAlgebra E.carrier a 0) =
      f (QuadraticAlgebra.omega : QuadraticAlgebra E.carrier a 0) by rfl]
  rw [show f (QuadraticAlgebra.omega : QuadraticAlgebra E.carrier a 0) = z by
    simp [f, QuadraticAlgebra.lift_apply_apply]]

end OrderedRealClosure
end RatFuncWittLocalGlobal
