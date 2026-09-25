/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Polynomial.Gcd
import RatFuncWittLocalGlobal.FiniteDimensional.Core
import RatFuncWittLocalGlobal.Ordering.Obstruction

/-!
# Squarefree polynomial normal forms for finite rational-function families

Each nonzero rational-function coefficient is obtained from a squarefree
polynomial coefficient by multiplying by a nonzero rational-function square.
The diagonal isotropy and finite strict-sign predicates are invariant under
this coordinatewise square scaling.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u

open Polynomial

/-- Decompose every nonzero rational-function coefficient through the
squarefree part of its numerator-denominator product. -/
theorem exists_squarefree_polynomial_normal_form
    {R : Type u} [Field R] {ι : Type*}
    (a : ι → _root_.RatFunc R) (ha : ∀ i, a i ≠ 0) :
    ∃ (A q : ι → Polynomial R) (y : ι → _root_.RatFunc R),
      (∀ i,
        A i ≠ 0 ∧ q i ≠ 0 ∧ Squarefree (A i) ∧
          (a i).num * (a i).denom = A i * q i ^ 2) ∧
        (∀ i,
          y i = algebraMap (Polynomial R) (_root_.RatFunc R) (q i) /
            algebraMap (Polynomial R) (_root_.RatFunc R) (a i).denom ∧
          y i ≠ 0 ∧
          a i = algebraMap (Polynomial R) (_root_.RatFunc R) (A i) * y i ^ 2) := by
  classical
  choose A q hA0 hq0 hAsq hP using fun i =>
    exists_squarefree_mul_square_of_ne_zero
      (mul_ne_zero (RatFunc.num_ne_zero (ha i)) (RatFunc.denom_ne_zero (a i)))
  let y : ι → _root_.RatFunc R := fun i =>
    algebraMap (Polynomial R) (_root_.RatFunc R) (q i) /
      algebraMap (Polynomial R) (_root_.RatFunc R) (a i).denom
  have hy : ∀ i, y i ≠ 0 := by
    intro i
    dsimp [y]
    exact div_ne_zero (RatFunc.algebraMap_ne_zero (hq0 i))
      (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero (a i)))
  have hdecomp : ∀ i,
      a i = algebraMap (Polynomial R) (_root_.RatFunc R) (A i) * y i ^ 2 := by
    intro i
    dsimp [y]
    calc
      a i = algebraMap (Polynomial R) (_root_.RatFunc R) (a i).num /
          algebraMap (Polynomial R) (_root_.RatFunc R) (a i).denom :=
        (RatFunc.num_div_denom (a i)).symm
      _ = algebraMap (Polynomial R) (_root_.RatFunc R) (A i) *
          (algebraMap (Polynomial R) (_root_.RatFunc R) (q i) /
            algebraMap (Polynomial R) (_root_.RatFunc R) (a i).denom) ^ 2 := by
        field_simp [RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero (a i))]
        simpa using congrArg (algebraMap (Polynomial R) (_root_.RatFunc R)) (hP i)
  refine ⟨A, q, y, ?_, ?_⟩
  · intro i
    exact ⟨hA0 i, hq0 i, hAsq i, hP i⟩
  · intro i
    exact ⟨by rfl, hy i, hdecomp i⟩

/-- The squarefree normal form preserves both diagonal isotropy and finite
strict-sign orderability. -/
theorem exists_squarefree_polynomial_normal_form_with_invariants
    {R : Type u} [Field R] {ι : Type*} [Fintype ι]
    (a : ι → _root_.RatFunc R) (ha : ∀ i, a i ≠ 0) :
    ∃ (A q : ι → Polynomial R) (y : ι → _root_.RatFunc R),
      (∀ i,
        A i ≠ 0 ∧ q i ≠ 0 ∧ Squarefree (A i) ∧
          (a i).num * (a i).denom = A i * q i ^ 2) ∧
        (∀ i,
          y i = algebraMap (Polynomial R) (_root_.RatFunc R) (q i) /
            algebraMap (Polynomial R) (_root_.RatFunc R) (a i).denom ∧
          y i ≠ 0 ∧
          a i = algebraMap (Polynomial R) (_root_.RatFunc R) (A i) * y i ^ 2) ∧
        (Diagonal.Isotropic a ↔
          Diagonal.Isotropic (fun i =>
            algebraMap (Polynomial R) (_root_.RatFunc R) (A i))) ∧
        (FiniteSameStrictSignOrdering a ↔
          FiniteSameStrictSignOrdering (fun i =>
            algebraMap (Polynomial R) (_root_.RatFunc R) (A i))) := by
  obtain ⟨A, q, y, hpoly, hydata⟩ :=
    exists_squarefree_polynomial_normal_form (R := R) a ha
  have hy : ∀ i, y i ≠ 0 := fun i => (hydata i).2.1
  have hdecomp : ∀ i,
      a i = algebraMap (Polynomial R) (_root_.RatFunc R) (A i) * y i ^ 2 :=
    fun i => (hydata i).2.2
  have ha_eq : a = fun i =>
      algebraMap (Polynomial R) (_root_.RatFunc R) (A i) * y i ^ 2 :=
    funext hdecomp
  have h_iso :
      Diagonal.Isotropic a ↔
        Diagonal.Isotropic (fun i =>
          algebraMap (Polynomial R) (_root_.RatFunc R) (A i)) := by
    rw [ha_eq]
    exact Diagonal.isotropic_mul_square hy
  have h_order :
      FiniteSameStrictSignOrdering a ↔
        FiniteSameStrictSignOrdering (fun i =>
          algebraMap (Polynomial R) (_root_.RatFunc R) (A i)) := by
    rw [ha_eq]
    exact finiteSameStrictSignOrdering_mul_square hy
  exact ⟨A, q, y, hpoly, hydata, h_iso, h_order⟩

end RatFunc

end RatFuncWittLocalGlobal
