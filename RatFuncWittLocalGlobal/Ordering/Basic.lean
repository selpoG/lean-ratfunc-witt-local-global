/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Mathlib.Algebra.Order.Ring.Ordering.Basic
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Ordered fields from ring orderings

This file records the elementary bridge from Mathlib's bundled
`RingPreordering.IsOrdering` API to the ordinary ordered-field typeclass API.
-/

namespace RatFuncWittLocalGlobal

namespace RingPreordering

variable {F : Type*} [Field F]
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Strict positivity with respect to a ring ordering. -/
def StrictPos (P : _root_.RingPreordering F) (x : F) : Prop :=
  x ∈ P ∧ -x ∉ P

theorem StrictPos.mem
    {P : _root_.RingPreordering F} {x : F} (hx : StrictPos P x) :
    x ∈ P :=
  hx.1

theorem StrictPos.neg_notMem
    {P : _root_.RingPreordering F} {x : F} (hx : StrictPos P x) :
    -x ∉ P :=
  hx.2

theorem StrictPos.ne_zero
    {P : _root_.RingPreordering F} {x : F} (hx : StrictPos P x) :
    x ≠ 0 := by
  intro hx0
  exact hx.neg_notMem (by simp [hx0])

theorem StrictPos.mul
    {P : _root_.RingPreordering F} {x y : F}
    (hx : StrictPos P x) (hy : StrictPos P y) :
    StrictPos P (x * y) := by
  refine ⟨mul_mem hx.mem hy.mem, ?_⟩
  intro hneg
  have hzero : x * y = 0 :=
    _root_.RingPreordering.eq_zero_of_mem_of_neg_mem
      (P := P) (x := x * y) (mul_mem hx.mem hy.mem) hneg
  rcases mul_eq_zero.mp hzero with hx0 | hy0
  · exact hx.ne_zero hx0
  · exact hy.ne_zero hy0

theorem strictPos_pow_two
    {P : _root_.RingPreordering F} {x : F} (hx : x ≠ 0) :
    StrictPos P (x ^ 2) := by
  refine ⟨_root_.RingPreordering.pow_two_mem P x, ?_⟩
  intro hneg
  have hzero : x ^ 2 = 0 :=
    _root_.RingPreordering.eq_zero_of_mem_of_neg_mem
      (P := P) (x := x ^ 2) (_root_.RingPreordering.pow_two_mem P x) hneg
  exact hx (eq_zero_of_pow_eq_zero hzero)

/-- Pull back the nonnegative cone along a field homomorphism. -/
def comapNonnegative (f : F →+* K) : _root_.RingPreordering F where
  carrier := {x | 0 ≤ f x}
  zero_mem' := by simp
  add_mem' hx hy := by
    simpa using add_nonneg hx hy
  one_mem' := by simp
  mul_mem' hx hy := by
    simpa using mul_nonneg hx hy
  mem_of_isSquare' := by
    rintro x ⟨y, rfl⟩
    simpa [pow_two] using sq_nonneg (f y)
  neg_one_notMem' := by
    norm_num

theorem mem_comapNonnegative_iff (f : F →+* K) {x : F} :
    x ∈ comapNonnegative f ↔ 0 ≤ f x :=
  Iff.rfl

instance comapNonnegative_isOrdering (f : F →+* K) :
    (comapNonnegative f).IsOrdering := by
  rw [_root_.RingPreordering.isOrdering_iff]
  intro a b hneg
  by_contra h
  push Not at h
  have ha : f a < 0 := lt_of_not_ge h.1
  have hb : f b < 0 := lt_of_not_ge h.2
  have hab_pos : 0 < f (a * b) := by
    simpa using mul_pos_of_neg_of_neg ha hb
  have hab_nonpos : f (a * b) ≤ 0 := by
    simpa [mem_comapNonnegative_iff] using hneg
  exact not_lt_of_ge hab_nonpos hab_pos

/-- The nonnegative cone of an ordered field, bundled as a ring preordering. -/
def nonnegative
    (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] :
    _root_.RingPreordering F where
  carrier := {x | 0 ≤ x}
  zero_mem' := le_rfl
  add_mem' hx hy := add_nonneg hx hy
  one_mem' := zero_le_one
  mul_mem' hx hy := mul_nonneg hx hy
  mem_of_isSquare' := by
    rintro x ⟨y, rfl⟩
    simpa [pow_two] using sq_nonneg y
  neg_one_notMem' := by
    norm_num

theorem mem_nonnegative_iff
    [LinearOrder F] [IsStrictOrderedRing F] {x : F} :
    x ∈ nonnegative F ↔ 0 ≤ x :=
  Iff.rfl

instance nonnegative_isOrdering
    [LinearOrder F] [IsStrictOrderedRing F] :
    (nonnegative F).IsOrdering := by
  rw [_root_.RingPreordering.isOrdering_iff]
  intro a b hneg
  by_contra h
  push Not at h
  have ha : a < 0 := lt_of_not_ge h.1
  have hb : b < 0 := lt_of_not_ge h.2
  have hab_pos : 0 < a * b := mul_pos_of_neg_of_neg ha hb
  have hab_nonpos : a * b ≤ 0 := by
    simpa [mem_nonnegative_iff] using hneg
  exact not_lt_of_ge hab_nonpos hab_pos

@[reducible]
noncomputable def linearOrderOfIsOrdering
    (P : _root_.RingPreordering F) [P.IsOrdering] : LinearOrder F where
  le x y := y - x ∈ P
  lt x y := y - x ∈ P ∧ x - y ∉ P
  le_refl x := by
    simp
  le_trans x y z hxy hyz := by
    have hsum : (y - x) + (z - y) ∈ P := add_mem hxy hyz
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
  lt_iff_le_not_ge x y := Iff.rfl
  le_antisymm x y hxy hyx := by
    have hneg : -(y - x) ∈ P := by
      simpa [sub_eq_add_neg, add_comm] using hyx
    exact (sub_eq_zero.mp
      (_root_.RingPreordering.eq_zero_of_mem_of_neg_mem (P := P) (x := y - x) hxy hneg)).symm
  le_total x y := by
    rcases mem_or_neg_mem P (y - x) with h | h
    · exact Or.inl h
    · right
      simpa [sub_eq_add_neg, add_comm] using h
  toDecidableLE := Classical.decRel _
  toDecidableEq := Classical.decEq F
  toDecidableLT := Classical.decRel _

theorem le_linearOrderOfIsOrdering_iff
    (P : _root_.RingPreordering F) [P.IsOrdering] {x y : F} :
    @LE.le F (linearOrderOfIsOrdering P).toLE x y ↔ y - x ∈ P :=
  Iff.rfl

theorem lt_linearOrderOfIsOrdering_iff
    (P : _root_.RingPreordering F) [P.IsOrdering] {x y : F} :
    @LT.lt F (linearOrderOfIsOrdering P).toLT x y ↔ y - x ∈ P ∧ x - y ∉ P :=
  Iff.rfl

theorem zero_le_linearOrderOfIsOrdering_iff
    (P : _root_.RingPreordering F) [P.IsOrdering] {x : F} :
    @LE.le F (linearOrderOfIsOrdering P).toLE 0 x ↔ x ∈ P := by
  rw [le_linearOrderOfIsOrdering_iff P]
  simp

theorem zero_lt_linearOrderOfIsOrdering_iff
    (P : _root_.RingPreordering F) [P.IsOrdering] {x : F} :
    @LT.lt F (linearOrderOfIsOrdering P).toLT 0 x ↔ x ∈ P ∧ -x ∉ P := by
  rw [lt_linearOrderOfIsOrdering_iff P]
  simp

theorem strictPos_iff_zero_lt_linearOrderOfIsOrdering
    (P : _root_.RingPreordering F) [P.IsOrdering] {x : F} :
    StrictPos P x ↔ @LT.lt F (linearOrderOfIsOrdering P).toLT 0 x :=
  (zero_lt_linearOrderOfIsOrdering_iff P).symm

theorem isStrictOrderedRingOfIsOrdering
    (P : _root_.RingPreordering F) [P.IsOrdering] :
    @IsStrictOrderedRing F _ (linearOrderOfIsOrdering P).toPartialOrder := by
  classical
  let _ : LinearOrder F := linearOrderOfIsOrdering P
  let _ : IsOrderedAddMonoid F := {
    add_le_add_left := fun a b hab c => by
      change b - a ∈ P at hab
      change (b + c) - (a + c) ∈ P
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hab }
  let _ : ZeroLEOneClass F := {
    zero_le_one := by
      change (1 : F) - 0 ∈ P
      simp }
  exact IsStrictOrderedRing.of_mul_pos (fun a b ha hb => by
    rw [lt_linearOrderOfIsOrdering_iff P] at ha hb ⊢
    have haP : a ∈ P := by
      simpa using ha.1
    have hbP : b ∈ P := by
      simpa using hb.1
    have habP : a * b ∈ P := mul_mem haP hbP
    refine ⟨by simpa using habP, ?_⟩
    intro hneg
    have hab_zero : a * b = 0 :=
      _root_.RingPreordering.eq_zero_of_mem_of_neg_mem habP (by simpa using hneg)
    rcases mul_eq_zero.mp hab_zero with ha_zero | hb_zero
    · exact ha.2 (by simp [ha_zero])
    · exact hb.2 (by simp [hb_zero]))

end RingPreordering
end RatFuncWittLocalGlobal
