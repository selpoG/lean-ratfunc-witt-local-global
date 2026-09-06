/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.RealClosure.Quadratic.Transport
import RatFuncWittLocalGlobal.RealClosure.Adjoin
import RatFuncWittLocalGlobal.Ordering.Extension
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# The real projection of a quadratic adjunction

For a quadratic algebra `QuadraticAlgebra K a 0`, the first coordinate is a
`K`-linear map.  Transporting this map through the algebra equivalence used by
the quadratic adjunction gives a projection on the simple adjoin.  Its value
on a square is the familiar expression `x² + a y²`; when `a` is positive this
expression is positive for every nonzero element.
-/

namespace RatFuncWittLocalGlobal
namespace OrderedRealClosure

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

local notation "Ω" => AlgebraicClosure F

/-! The real-coordinate projection in the quadratic algebra. -/

def quadraticReLinearMap {K : Type*} [Semiring K] (a : K) :
    QuadraticAlgebra K a 0 →ₗ[K] K :=
  QuadraticAlgebra.reₗ a 0

@[simp] theorem quadraticReLinearMap_apply {K : Type*} [Semiring K] (a : K)
    (w : QuadraticAlgebra K a 0) :
    quadraticReLinearMap a w = w.re :=
  rfl

/-! Transport the real-coordinate projection across an algebra equivalence. -/

def quadraticProjection {K L : Type*} [CommSemiring K] [Semiring L]
    [Algebra K L] {a : K}
    (e : QuadraticAlgebra K a 0 ≃ₐ[K] L) : L →ₗ[K] K :=
  (quadraticReLinearMap a).comp e.symm.toLinearMap

@[simp] theorem quadraticProjection_apply {K L : Type*} [CommSemiring K] [Semiring L]
    [Algebra K L] {a : K}
    (e : QuadraticAlgebra K a 0 ≃ₐ[K] L) (z : L) :
    quadraticProjection e z = (e.symm z).re :=
  rfl

/-!
The square formula is stated with the coordinates of `e.symm z` explicit so
that it can be consumed directly by the later sign criterion.
-/

theorem quadraticProjection_mul_self_eq {K L : Type*} [CommSemiring K] [Semiring L]
    [Algebra K L] {a : K}
    (e : QuadraticAlgebra K a 0 ≃ₐ[K] L) {z : L} {x y : K}
    (hz : e.symm z = (⟨x, y⟩ : QuadraticAlgebra K a 0)) :
    quadraticProjection e (z * z) = x ^ 2 + a * y ^ 2 := by
  change (e.symm (z * z)).re = _
  rw [map_mul, hz]
  simp only [QuadraticAlgebra.re_mul]
  ring

theorem quadraticProjection_mul_self_pos {K L : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Field L] [Algebra K L] {a : K}
    (e : QuadraticAlgebra K a 0 ≃ₐ[K] L) {z : L}
    (ha : 0 < a) (hz : z ≠ 0) :
    0 < quadraticProjection e (z * z) := by
  let w : QuadraticAlgebra K a 0 := e.symm z
  have hw : w ≠ 0 := by
    intro hw0
    apply hz
    calc
      z = e (e.symm z) := (e.apply_symm_apply z).symm
      _ = e 0 := by
        rw [show e.symm z = 0 by simpa [w] using hw0]
      _ = 0 := map_zero e
  have hcoord : w.re ≠ 0 ∨ w.im ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    exact QuadraticAlgebra.ext h.1 h.2
  have hformula :
      quadraticProjection e (z * z) = w.re ^ 2 + a * w.im ^ 2 := by
    apply quadraticProjection_mul_self_eq e
    rfl
  rw [hformula]
  rcases hcoord with hreal | himag
  · have hreal_pos : 0 < w.re ^ 2 := sq_pos_of_ne_zero hreal
    have himag_nonneg : 0 ≤ a * w.im ^ 2 :=
      mul_nonneg ha.le (sq_nonneg w.im)
    exact add_pos_of_pos_of_nonneg hreal_pos himag_nonneg
  · have hreal_nonneg : 0 ≤ w.re ^ 2 := sq_nonneg w.re
    have himag_pos : 0 < a * w.im ^ 2 :=
      mul_pos ha (sq_pos_of_ne_zero himag)
    exact add_pos_of_nonneg_of_pos hreal_nonneg himag_pos

/-!
### An ordered quadratic adjunction

The projection positivity theorem feeds the general base/squares ordering
construction.  Since the latter exposes the induced order by its explicit
`LinearOrder` object, the monotonicity conclusion below uses that same order
object explicitly.
-/

theorem exists_ordered_quadratic_adjoin
    (E : Intermediate F) {a : E.carrier} {α : Ω}
    (ha : 0 < a) (hα : α ^ 2 = (a : Ω)) (hnsq : ¬ IsSquare a) :
    ∃ (O : RingPreordering (IntermediateField.adjoin E.carrier ({α} : Set Ω)))
      (hO : O.IsOrdering),
      ∀ ⦃x y : E.carrier⦄, x ≤ y →
        @LE.le (IntermediateField.adjoin E.carrier ({α} : Set Ω))
          (@RingPreordering.linearOrderOfIsOrdering
            (IntermediateField.adjoin E.carrier ({α} : Set Ω)) _ O hO).toLE
          (algebraMap E.carrier (IntermediateField.adjoin E.carrier ({α} : Set Ω)) x)
          (algebraMap E.carrier (IntermediateField.adjoin E.carrier ({α} : Set Ω)) y) := by
  let L : IntermediateField E.carrier Ω :=
    IntermediateField.adjoin E.carrier ({α} : Set Ω)
  obtain ⟨e, he⟩ := quadraticAdjoinAlgEquiv (F := F) hα hnsq
  let π : L →ₗ[E.carrier] E.carrier := quadraticProjection e
  have hπ : ∀ z : L, z ≠ 0 → 0 < π (z * z) := by
    intro z hz
    exact quadraticProjection_mul_self_pos e ha hz
  obtain ⟨O, hO, _, _, hmono⟩ :=
    RingPreordering.exists_orderedAlgebraExtension_with_algebraMap_monotone_of_projection
      π hπ
  refine ⟨O, hO, ?_⟩
  intro x y hxy
  exact hmono hxy

/-!
### Maximal ordered intermediates contain square roots of nonnegative elements

The quadratic extension above is enough to rule out a positive nonsquare in a
maximal ordered intermediate field.  The zero case is handled directly; in the
nonzero case the square-root adjunction strictly extends the carrier unless
the root was already present, while maximality forces the latter.
-/

theorem nonnegative_isSquare_of_isMax
    (M : Intermediate F) (hmax : IsMax M) {a : M.carrier}
    (ha : 0 ≤ a) : IsSquare a := by
  by_cases ha0 : a = 0
  · exact ⟨0, by simp [ha0]⟩
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  by_contra hsq
  obtain ⟨α, hα⟩ := exists_square_root F (a : Ω)
  have hα0 : α ≠ 0 := by
    intro hzero
    apply ha0
    apply Subtype.ext
    change (a : Ω) = (0 : Ω)
    rw [← hα, hzero]
    simp
  let L : IntermediateField M.carrier Ω :=
    IntermediateField.adjoin M.carrier ({α} : Set Ω)
  obtain ⟨O, hO, hmono_explicit⟩ :=
    exists_ordered_quadratic_adjoin (F := F) M ha_pos hα hsq
  let _ : O.IsOrdering := hO
  let _ : LinearOrder L := RingPreordering.linearOrderOfIsOrdering O
  let _ : IsStrictOrderedRing L := RingPreordering.isStrictOrderedRingOfIsOrdering O
  have hmono : Monotone (algebraMap M.carrier L) := by
    intro x y hxy
    exact hmono_explicit hxy
  let _ : IsOrderedModule M.carrier L :=
    IsOrderedModule.of_algebraMap_mono hmono
  have hMLE : M ≤ M.ofOrderedSubfield L :=
    Intermediate.le_ofOrderedSubfield (F := F) M L
  have hαL : α ∈ L := by
    change α ∈ IntermediateField.adjoin M.carrier ({α} : Set Ω)
    exact IntermediateField.mem_adjoin_of_mem M.carrier (Set.mem_singleton α)
  have hαE : α ∈ (M.ofOrderedSubfield L).carrier := by
    change α ∈ IntermediateField.restrictScalars F L
    exact hαL
  have hαM : α ∈ M.carrier :=
    maximal_contains_of_le (F := F) hmax hMLE hαE
  let b : M.carrier := ⟨α, hαM⟩
  have hb : a = b * b := by
    apply Subtype.ext
    change (a : Ω) = (α * α : Ω)
    simpa [pow_two] using hα.symm
  exact hsq ⟨b, hb⟩

end OrderedRealClosure
end RatFuncWittLocalGlobal
