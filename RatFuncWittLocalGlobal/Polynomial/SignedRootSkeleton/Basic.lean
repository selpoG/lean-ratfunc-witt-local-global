/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Polynomial.InfinitySign
import Mathlib.Algebra.Squarefree.Basic

/-!
# Signed products of distinct linear factors

This file packages a nonzero scalar times a product of distinct real linear
factors. It is the dimension-independent polynomial skeleton used by the
compression argument.
-/

namespace RatFuncWittLocalGlobal

open scoped BigOperators
open _root_.Polynomial

universe u

noncomputable section

/-- A nonzero scalar together with the finite set of its simple real roots. -/
structure SignedLinearRootSkeleton (R : Type u) [Field R] where
  roots : Finset R
  scale : R
  scale_ne_zero : scale ≠ 0

namespace SignedLinearRootSkeleton

variable {R : Type u} [Field R]

local instance : DecidableEq R := Classical.decEq R

/-- Signed skeletons are determined by their root set and scale. -/
@[ext]
theorem ext {S T : SignedLinearRootSkeleton R}
    (hroots : S.roots = T.roots) (hscale : S.scale = T.scale) : S = T := by
  cases S
  cases T
  cases hroots
  cases hscale
  rfl

/-- The polynomial represented by a signed linear-root skeleton. -/
def poly (S : SignedLinearRootSkeleton R) : Polynomial R :=
  C S.scale * ∏ r ∈ S.roots, (X - C r)

private theorem linearFactors_squarefree (S : SignedLinearRootSkeleton R) :
    Squarefree (∏ r ∈ S.roots, (X - C r : Polynomial R)) := by
  classical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro x hx y hy hxy
    exact (isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hxy).isUnit).isRelPrime
  · intro r _
    exact (prime_X_sub_C r).squarefree

/-- The skeleton polynomial is squarefree. -/
theorem poly_squarefree (S : SignedLinearRootSkeleton R) : Squarefree S.poly := by
  rw [poly, squarefree_mul_iff]
  exact ⟨(isUnit_C.mpr S.scale_ne_zero.isUnit).isRelPrime_left,
    (isUnit_C.mpr S.scale_ne_zero.isUnit).squarefree, S.linearFactors_squarefree⟩

/-- The skeleton polynomial is nonzero. -/
theorem poly_ne_zero (S : SignedLinearRootSkeleton R) : S.poly ≠ 0 :=
  S.poly_squarefree.ne_zero

/-- Evaluating the skeleton polynomial exposes its signed product formula. -/
@[simp]
theorem eval_poly (S : SignedLinearRootSkeleton R) (x : R) :
    S.poly.eval x = S.scale * ∏ r ∈ S.roots, (x - r) := by
  rw [poly, eval_mul, eval_C, eval_prod]
  simp

/-- The roots of the skeleton polynomial are exactly its recorded roots. -/
@[simp]
theorem eval_poly_eq_zero_iff (S : SignedLinearRootSkeleton R) (x : R) :
    S.poly.eval x = 0 ↔ x ∈ S.roots := by
  classical
  rw [eval_poly, mul_eq_zero, Finset.prod_eq_zero_iff]
  simp only [S.scale_ne_zero, false_or]
  constructor
  · rintro ⟨r, hr, hxr⟩
    simpa [sub_eq_zero.mp hxr] using hr
  · intro hx
    exact ⟨x, hx, sub_self x⟩

/-- The polynomial left after removing the recorded linear factor at `r`. -/
def cofactorAt (S : SignedLinearRootSkeleton R) (r : R) : Polynomial R :=
  by
    classical
    exact C S.scale * ∏ s ∈ S.roots.erase r, (X - C s)

/-- A recorded root factors out with the explicit cofactor. -/
theorem poly_eq_X_sub_C_mul_cofactorAt (S : SignedLinearRootSkeleton R)
    {r : R} (hr : r ∈ S.roots) :
    S.poly = (X - C r) * S.cofactorAt r := by
  classical
  rw [poly, cofactorAt, ← Finset.mul_prod_erase S.roots (fun s => X - C s) hr]
  ring

@[simp]
theorem eval_cofactorAt (S : SignedLinearRootSkeleton R) (r : R) :
    (S.cofactorAt r).eval r =
      S.scale * ∏ s ∈ S.roots.erase r, (r - s) := by
  classical
  rw [cofactorAt, eval_mul, eval_C, eval_prod]
  simp

/-- The cofactor is a unit at every recorded simple root. -/
theorem eval_cofactorAt_ne_zero (S : SignedLinearRootSkeleton R)
    (r : R) :
    (S.cofactorAt r).eval r ≠ 0 := by
  classical
  rw [eval_cofactorAt, mul_ne_zero_iff]
  refine ⟨S.scale_ne_zero, Finset.prod_ne_zero_iff.mpr ?_⟩
  intro s hs
  exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm

end SignedLinearRootSkeleton
end
end RatFuncWittLocalGlobal
