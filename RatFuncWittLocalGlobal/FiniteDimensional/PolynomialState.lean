/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.FiniteDimensional.PolynomialNormalForm
import RatFuncWittLocalGlobal.FiniteDimensional.ScalarSign
import RatFuncWittLocalGlobal.Polynomial.LaurentPoint

/-!
# Polynomial states for finite diagonal families

This module records the dimension-independent polynomial state for the
binary-tail induction: squarefree representatives, preserved isotropy and
ordering predicates, and the finite set of all real coefficient roots.
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u

noncomputable section

/-- Squarefree polynomial data for a regular finite rational-function family
with no common strict-sign ordering. -/
structure FinitePolynomialState
    {R : Type u} [Field R] {ι : Type*} [Fintype ι]
    (a : ι → _root_.RatFunc R) where
  A : ι → Polynomial R
  q : ι → Polynomial R
  y : ι → _root_.RatFunc R
  normal_form : ∀ i,
    A i ≠ 0 ∧ q i ≠ 0 ∧ Squarefree (A i) ∧
      (a i).num * (a i).denom = A i * q i ^ 2
  decomposition : ∀ i,
    y i = algebraMap (Polynomial R) (_root_.RatFunc R) (q i) /
        (a i).denom ∧
      y i ≠ 0 ∧
      a i = algebraMap (Polynomial R) (_root_.RatFunc R) (A i) * y i ^ 2
  isotropy_iff :
    Diagonal.Isotropic a ↔
      Diagonal.Isotropic (fun i =>
        algebraMap (Polynomial R) (_root_.RatFunc R) (A i))
  ordering_iff :
    RatFunc.FiniteSameStrictSignOrdering a ↔
      RatFunc.FiniteSameStrictSignOrdering (fun i =>
        algebraMap (Polynomial R) (_root_.RatFunc R) (A i))
  hno : ¬ RatFunc.FiniteSameStrictSignOrdering (fun i =>
    algebraMap (Polynomial R) (_root_.RatFunc R) (A i))

/-- Every regular finite family with the ordering obstruction has a
squarefree polynomial state. -/
theorem finitePolynomialState_exists
    {R : Type u} [Field R] {ι : Type*} [Fintype ι]
    {a : ι → _root_.RatFunc R}
    (ha : ∀ i, a i ≠ 0)
    (hno : ¬ RatFunc.FiniteSameStrictSignOrdering a) :
    Nonempty (FinitePolynomialState a) := by
  rcases RatFunc.exists_squarefree_polynomial_normal_form_with_invariants
      a ha with ⟨A, q, y, hpoly, hydata, hiso, horder⟩
  exact ⟨{
    A := A
    q := q
    y := y
    normal_form := hpoly
    decomposition := hydata
    isotropy_iff := hiso
    ordering_iff := horder
    hno := fun h => hno (horder.mpr h)
  }⟩

/-- All ordinary real roots of a finite polynomial coefficient family. -/
noncomputable def FinitePolynomialState.realRoots
    {R : Type u} [Field R] {ι : Type*} [Fintype ι]
    {a : ι → _root_.RatFunc R}
    (T : FinitePolynomialState a) : Finset R := by
  classical
  exact Finset.univ.biUnion fun i => (T.A i).roots.toFinset

/-- Membership in the breakpoint set is membership in the root set of some
coefficient. -/
theorem FinitePolynomialState.mem_realRoots_iff
    {R : Type u} [Field R] {ι : Type*} [Fintype ι]
    {a : ι → _root_.RatFunc R}
    (T : FinitePolynomialState a) (r : R) :
    r ∈ T.realRoots ↔ ∃ i, (T.A i).eval r = 0 := by
  classical
  simp only [FinitePolynomialState.realRoots, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Multiset.mem_toFinset]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (mem_roots (T.normal_form i).1).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (mem_roots (T.normal_form i).1).mpr hi⟩

/-- Away from the breakpoint set, every coefficient evaluates nontrivially. -/
theorem FinitePolynomialState.eval_ne_zero_of_not_mem_realRoots
    {R : Type u} [Field R] {ι : Type*} [Fintype ι]
    {a : ι → _root_.RatFunc R}
    (T : FinitePolynomialState a) {r : R}
    (hr : r ∉ T.realRoots) (i : ι) :
    (T.A i).eval r ≠ 0 := by
  intro hz
  exact hr ((T.mem_realRoots_iff r).mpr ⟨i, hz⟩)

/-- The normalized family remains nondefinite after every ordered field
embedding of the rational function field. -/
theorem FinitePolynomialState.not_scalarFamilySameStrictSign_map
    {R : Type u} [Field R] {ι : Type*} [Fintype ι]
    {a : ι → _root_.RatFunc R}
    (T : FinitePolynomialState a)
    {L : Type u} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (f : _root_.RatFunc R →+* L) :
    ¬ ScalarFamilySameStrictSign (fun i =>
      f (algebraMap (Polynomial R) (_root_.RatFunc R) (T.A i))) := by
  intro hsame
  apply T.hno
  rcases hsame with hpos | hneg
  · exact RatFunc.finiteSameStrictSignOrdering_of_hom_all_pos f hpos
  · exact RatFunc.finiteSameStrictSignOrdering_of_hom_all_neg f hneg

end

end RatFuncWittLocalGlobal
