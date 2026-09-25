/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Sign.Strict

/-!
# Dimension-independent sign propagation

These lemmas choose a prescribed sign up to negation and propagate a predicate
through consecutive points of a finite linear order.  They are shared by the
rank-specific and dimension-independent signed-skeleton constructions.
-/

namespace RatFuncWittLocalGlobal

universe u

namespace StrictSign

/-- A strict sign holds either on a nonzero scalar or on its negative. -/
theorem holds_or_holds_neg
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (sign : StrictSign) {x : R} (hx : x ≠ 0) :
    sign.Holds x ∨ sign.Holds (-x) := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · cases sign with
    | pos => exact Or.inr (neg_pos.mpr hxneg)
    | neg => exact Or.inl hxneg
  · cases sign with
    | pos => exact Or.inl hxpos
    | neg => exact Or.inr (neg_lt_zero.mpr hxpos)

/-- Two unequal strict signs are opposites. -/
theorem opposite_eq_of_ne (s t : StrictSign) (h : s ≠ t) :
    s.opposite = t := by
  cases s <;> cases t <;> simp [opposite] at h ⊢

end StrictSign

namespace Finset

/-- On a finite linear order, a predicate that is equivalent across every
consecutive pair propagates from the minimum to every element. -/
theorem forall_of_min'_of_consecutive_iff
    {α : Type*} [LinearOrder α] (s : Finset α) (P : α → Prop)
    (hstep : ∀ x ∈ s, ∀ y ∈ s, x < y →
      (∀ z ∈ s, ¬(x < z ∧ z < y)) → (P x ↔ P y))
    (hs : s.Nonempty) (hmin : P (s.min' hs)) :
    ∀ x ∈ s, P x := by
  induction s using Finset.induction_on_min with
  | empty => simp at hs
  | @insert a t hleast ih =>
      by_cases ht : t.Nonempty
      · have hab : a < t.min' ht := hleast _ (t.min'_mem ht)
        have hmin_eq : (insert a t).min' (t.insert_nonempty a) = a := by
          rw [Finset.min'_insert a t ht, min_eq_left hab.le]
        have ha : P a := by
          rw [← hmin_eq]
          exact hmin
        have hgap : ∀ z ∈ insert a t,
            ¬(a < z ∧ z < t.min' ht) := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hzt
          · simp
          · intro hzbetween
            exact (not_lt_of_ge (t.min'_le z hzt)) hzbetween.2
        have hb : P (t.min' ht) :=
          (hstep a (Finset.mem_insert_self a t) (t.min' ht)
            (Finset.mem_insert_of_mem (t.min'_mem ht)) hab hgap).mp ha
        have hstep_t : ∀ x ∈ t, ∀ y ∈ t, x < y →
            (∀ z ∈ t, ¬(x < z ∧ z < y)) → (P x ↔ P y) := by
          intro x hx y hy hxy hbetween
          apply hstep x (Finset.mem_insert_of_mem hx) y
            (Finset.mem_insert_of_mem hy) hxy
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hzt
          · exact fun haz => (not_lt_of_ge (hleast x hx).le) haz.1
          · exact hbetween z hzt
        have hall_t := ih hstep_t ht hb
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxt
        · exact ha
        · exact hall_t x hxt
      · have ht_empty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
        subst t
        simpa using hmin

end Finset

end RatFuncWittLocalGlobal
