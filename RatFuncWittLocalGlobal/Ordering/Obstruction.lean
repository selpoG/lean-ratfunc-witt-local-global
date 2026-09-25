/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Core.RealClosedDiagonal
import RatFuncWittLocalGlobal.Ordering.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# Ordering obstructions for diagonal forms

Ordering obstructions for normalized ternary forms and arbitrary finite
coefficient families, together with their real-closed-extension realizations.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v w z

/--
The sign obstruction for the normalized ternary form `⟨1, b, c⟩` vanishes if,
after mapping to every real closed extension, at least one of `b` and `c` is
nonpositive.
-/
def NormalizedSignObstructionFree
    {R : Type u} [Field R] (b c : RatFunc R) : Prop :=
  ∀ {K : Type v}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
    [Algebra (RatFunc R) K],
    algebraMap (RatFunc R) K b ≤ 0 ∨ algebraMap (RatFunc R) K c ≤ 0

/--
A concrete witness to failure of the normalized sign condition: a real closed
target field in which both non-leading coefficients are positive.
-/
structure NormalizedSignObstructionWitness
    {R : Type u} [Field R] (b c : RatFunc R) where
  K : Type v
  [field : Field K]
  [linearOrder : LinearOrder K]
  [strictOrdered : IsStrictOrderedRing K]
  [realClosed : IsRealClosed K]
  [algebra : Algebra (RatFunc R) K]
  pos_left : 0 < algebraMap (RatFunc R) K b
  pos_right : 0 < algebraMap (RatFunc R) K c

attribute [instance] NormalizedSignObstructionWitness.field
attribute [instance] NormalizedSignObstructionWitness.linearOrder
attribute [instance] NormalizedSignObstructionWitness.strictOrdered
attribute [instance] NormalizedSignObstructionWitness.realClosed
attribute [instance] NormalizedSignObstructionWitness.algebra

/-- There is a real closed target field where both coefficients are positive. -/
def HasNormalizedSignObstruction
    {R : Type u} [Field R] (b c : RatFunc R) : Prop :=
  Nonempty (NormalizedSignObstructionWitness.{u, v} b c)

/--
A concrete ordering on `RatFunc R` itself in which both normalized coefficients
are positive.
-/
structure OrderedRatFuncPositivePair
    {R : Type u} [Field R] (b c : RatFunc R) where
  [linearOrder : LinearOrder (RatFunc R)]
  [strictOrdered : IsStrictOrderedRing (RatFunc R)]
  pos_left : 0 < b
  pos_right : 0 < c

/--
An order-theoretic shadow of the sign obstruction: some ordering of `RatFunc R`
makes both normalized coefficients strictly positive.
-/
def NormalizedOrderingObstruction
    {R : Type u} [Field R] (b c : RatFunc R) : Prop :=
  ∃ P : _root_.RingPreordering (RatFunc R),
    P.IsOrdering ∧ b ∈ P ∧ -b ∉ P ∧ c ∈ P ∧ -c ∉ P

/--
An ordering where three coefficients have a common strict sign: either all are
strictly positive, or all are strictly negative.
-/
def SameStrictSignOrdering
    {R : Type u} [Field R] (a b c : RatFunc R) : Prop :=
  ∃ P : _root_.RingPreordering (RatFunc R),
    P.IsOrdering ∧
      ((RatFuncWittLocalGlobal.RingPreordering.StrictPos P a ∧
          RatFuncWittLocalGlobal.RingPreordering.StrictPos P b ∧
          RatFuncWittLocalGlobal.RingPreordering.StrictPos P c) ∨
        (RatFuncWittLocalGlobal.RingPreordering.StrictPos P (-a) ∧
          RatFuncWittLocalGlobal.RingPreordering.StrictPos P (-b) ∧
          RatFuncWittLocalGlobal.RingPreordering.StrictPos P (-c)))

/--
An ordering where a finite family of coefficients has a common strict sign:
either all coefficients are strictly positive, or all are strictly negative.
-/
def FiniteSameStrictSignOrdering
    {R : Type u} [Field R] {ι : Type w} (a : ι → RatFunc R) : Prop :=
  ∃ P : _root_.RingPreordering (RatFunc R),
    P.IsOrdering ∧
      ((∀ i, RatFuncWittLocalGlobal.RingPreordering.StrictPos P (a i)) ∨
        (∀ i, RatFuncWittLocalGlobal.RingPreordering.StrictPos P (-(a i))))

theorem finiteSameStrictSignOrdering_comp_equiv
    {R : Type u} [Field R] {ι : Type w} {κ : Type z}
    (e : ι ≃ κ) (a : κ → RatFunc R) :
    FiniteSameStrictSignOrdering (fun i : ι => a (e i)) ↔
      FiniteSameStrictSignOrdering a := by
  constructor
  · rintro ⟨P, hP, hsign⟩
    refine ⟨P, hP, ?_⟩
    rcases hsign with hpos | hneg
    · exact Or.inl fun k => by
        simpa using hpos (e.symm k)
    · exact Or.inr fun k => by
        simpa using hneg (e.symm k)
  · rintro ⟨P, hP, hsign⟩
    refine ⟨P, hP, ?_⟩
    rcases hsign with hpos | hneg
    · exact Or.inl fun i => hpos (e i)
    · exact Or.inr fun i => by
        simpa using hneg (e i)

theorem strictPos_comapNonnegative_of_pos
    {R : Type u} [Field R]
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : RatFunc R →+* K) {x : RatFunc R} (hx : 0 < f x) :
    RatFuncWittLocalGlobal.RingPreordering.StrictPos
      (RatFuncWittLocalGlobal.RingPreordering.comapNonnegative f) x := by
  refine ⟨le_of_lt hx, ?_⟩
  intro hneg
  change 0 ≤ f (-x) at hneg
  have hx_nonpos : f x ≤ 0 := by
    simpa using neg_nonneg.mp (by simpa using hneg)
  exact not_le_of_gt hx hx_nonpos

theorem sameStrictSignOrdering_of_hom_pos
    {R : Type u} [Field R]
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : RatFunc R →+* K) {a b c : RatFunc R}
    (ha : 0 < f a) (hb : 0 < f b) (hc : 0 < f c) :
    SameStrictSignOrdering a b c := by
  let P : _root_.RingPreordering (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.comapNonnegative f
  exact ⟨P, inferInstance, Or.inl
    ⟨strictPos_comapNonnegative_of_pos f ha,
      strictPos_comapNonnegative_of_pos f hb,
      strictPos_comapNonnegative_of_pos f hc⟩⟩

theorem sameStrictSignOrdering_of_hom_neg
    {R : Type u} [Field R]
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : RatFunc R →+* K) {a b c : RatFunc R}
    (ha : f a < 0) (hb : f b < 0) (hc : f c < 0) :
    SameStrictSignOrdering a b c := by
  let P : _root_.RingPreordering (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.comapNonnegative f
  have hna : 0 < f (-a) := by simpa using neg_pos.mpr ha
  have hnb : 0 < f (-b) := by simpa using neg_pos.mpr hb
  have hnc : 0 < f (-c) := by simpa using neg_pos.mpr hc
  exact ⟨P, inferInstance, Or.inr
    ⟨strictPos_comapNonnegative_of_pos f hna,
      strictPos_comapNonnegative_of_pos f hnb,
      strictPos_comapNonnegative_of_pos f hnc⟩⟩

theorem finiteSameStrictSignOrdering_of_hom_all_pos
    {R : Type u} [Field R] {ι : Type w}
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : RatFunc R →+* K) {a : ι → RatFunc R}
    (hpos : ∀ i, 0 < f (a i)) :
    FiniteSameStrictSignOrdering a := by
  let P : _root_.RingPreordering (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.comapNonnegative f
  exact ⟨P, inferInstance, Or.inl fun i =>
    strictPos_comapNonnegative_of_pos f (hpos i)⟩

theorem finiteSameStrictSignOrdering_of_hom_all_neg
    {R : Type u} [Field R] {ι : Type w}
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : RatFunc R →+* K) {a : ι → RatFunc R}
    (hneg : ∀ i, f (a i) < 0) :
    FiniteSameStrictSignOrdering a := by
  let P : _root_.RingPreordering (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.comapNonnegative f
  exact ⟨P, inferInstance, Or.inr fun i =>
    strictPos_comapNonnegative_of_pos f (by simpa using neg_pos.mpr (hneg i))⟩

theorem finiteSameStrictSignOrdering_of_hom_not_isotropic
    {R : Type u} [Field R] {ι : Type w} [Fintype ι] [Nonempty ι]
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
    (f : RatFunc R →+* K) {a : ι → RatFunc R}
    (hreg : ∀ i, a i ≠ 0)
    (haniso : ¬ Diagonal.Isotropic (fun i => f (a i))) :
    FiniteSameStrictSignOrdering a := by
  have hregK : ∀ i, f (a i) ≠ 0 := fun i => by
    simpa using f.injective.ne (hreg i)
  rcases (Diagonal.not_isotropic_iff_all_pos_or_all_neg
    (a := fun i => f (a i)) hregK).mp haniso with hpos | hneg
  · exact finiteSameStrictSignOrdering_of_hom_all_pos f hpos
  · exact finiteSameStrictSignOrdering_of_hom_all_neg f hneg

theorem finiteSameStrictSignOrdering_mul_square
    {R : Type u} [Field R] {ι : Type w}
    {a r : ι → RatFunc R} (hr : ∀ i, r i ≠ 0) :
    FiniteSameStrictSignOrdering (fun i => a i * r i ^ 2) ↔
      FiniteSameStrictSignOrdering a := by
  constructor
  · rintro ⟨P, hP, hsign⟩
    refine ⟨P, hP, ?_⟩
    rcases hsign with hpos | hneg
    · refine Or.inl ?_
      intro i
      have hinv :
          RatFuncWittLocalGlobal.RingPreordering.StrictPos P ((r i)⁻¹ ^ 2) :=
        RatFuncWittLocalGlobal.RingPreordering.strictPos_pow_two (inv_ne_zero (hr i))
      have hscaled := (hpos i).mul hinv
      simpa [pow_two, mul_assoc, hr i] using hscaled
    · refine Or.inr ?_
      intro i
      have hinv :
          RatFuncWittLocalGlobal.RingPreordering.StrictPos P ((r i)⁻¹ ^ 2) :=
        RatFuncWittLocalGlobal.RingPreordering.strictPos_pow_two (inv_ne_zero (hr i))
      have hscaled := (hneg i).mul hinv
      simpa [pow_two, mul_assoc, hr i] using hscaled
  · rintro ⟨P, hP, hsign⟩
    refine ⟨P, hP, ?_⟩
    rcases hsign with hpos | hneg
    · refine Or.inl ?_
      intro i
      have hsqr :
          RatFuncWittLocalGlobal.RingPreordering.StrictPos P (r i ^ 2) :=
        RatFuncWittLocalGlobal.RingPreordering.strictPos_pow_two (hr i)
      exact (hpos i).mul hsqr
    · refine Or.inr ?_
      intro i
      have hsqr :
          RatFuncWittLocalGlobal.RingPreordering.StrictPos P (r i ^ 2) :=
        RatFuncWittLocalGlobal.RingPreordering.strictPos_pow_two (hr i)
      have hscaled := (hneg i).mul hsqr
      simpa [neg_mul] using hscaled

theorem not_finiteSameStrictSignOrdering_of_isotropic
    {R : Type u} [Field R] {ι : Type w} [Fintype ι]
    (a : ι → RatFunc R) (hiso : Diagonal.Isotropic a) :
    ¬ FiniteSameStrictSignOrdering a := by
  rintro ⟨P, hP, hsign⟩
  have _ : P.IsOrdering := hP
  let _ : LinearOrder (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.linearOrderOfIsOrdering P
  let _ : IsStrictOrderedRing (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.isStrictOrderedRingOfIsOrdering P
  rcases hsign with hposP | hnegP
  · have hpos : ∀ i, 0 < a i := by
      intro i
      exact
        (RatFuncWittLocalGlobal.RingPreordering.strictPos_iff_zero_lt_linearOrderOfIsOrdering
          P).mp (hposP i)
    exact (Diagonal.not_isotropic_of_all_pos hpos) hiso
  · have hneg : ∀ i, a i < 0 := by
      intro i
      have hneg_pos : 0 < -(a i) :=
        (RatFuncWittLocalGlobal.RingPreordering.strictPos_iff_zero_lt_linearOrderOfIsOrdering
          P).mp (hnegP i)
      exact neg_pos.mp hneg_pos
    exact (Diagonal.not_isotropic_of_all_neg hneg) hiso

theorem sameStrictSignOrdering_of_ternary_hom_not_isotropic
    {R : Type u} [Field R]
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
    (f : RatFunc R →+* K) {a b c : RatFunc R}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (haniso : ¬ Diagonal.TernaryIsotropic (f a) (f b) (f c)) :
    SameStrictSignOrdering a b c := by
  let coeff : Fin 3 → K := ![f a, f b, f c]
  have hreg : ∀ i, coeff i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [coeff] using f.injective.ne ha
    · simpa [coeff] using f.injective.ne hb
    · simpa [coeff] using f.injective.ne hc
  have haniso_fin : ¬ Diagonal.Isotropic coeff := by
    intro h
    exact haniso (by
      simpa [coeff] using (Diagonal.isotropic_fin_three_iff coeff).mp h)
  rcases (Diagonal.not_isotropic_iff_all_pos_or_all_neg (a := coeff) hreg).mp haniso_fin
    with hpos | hneg
  · exact sameStrictSignOrdering_of_hom_pos f
      (by simpa [coeff] using hpos 0)
      (by simpa [coeff] using hpos 1)
      (by simpa [coeff] using hpos 2)
  · exact sameStrictSignOrdering_of_hom_neg f
      (by simpa [coeff] using hneg 0)
      (by simpa [coeff] using hneg 1)
      (by simpa [coeff] using hneg 2)

theorem sameStrictSignOrdering_of_ternary_not_isotropic
    {R : Type u} [Field R]
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
    [Algebra (RatFunc R) K] {a b c : RatFunc R}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (haniso :
      ¬ Diagonal.TernaryIsotropic
        (algebraMap (RatFunc R) K a)
        (algebraMap (RatFunc R) K b)
        (algebraMap (RatFunc R) K c)) :
    SameStrictSignOrdering a b c :=
  sameStrictSignOrdering_of_ternary_hom_not_isotropic
    (algebraMap (RatFunc R) K) ha hb hc haniso

theorem ternaryLocallyIsotropic_of_not_sameStrictSignOrdering
    {R : Type u} [Field R] {a b c : RatFunc R}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hno : ¬ SameStrictSignOrdering a b c) :
    TernaryLocallyIsotropic.{u, v} a b c := by
  intro K _ _ _ _ _
  by_contra haniso
  exact hno (sameStrictSignOrdering_of_ternary_not_isotropic ha hb hc haniso)

theorem normalizedOrderingObstruction_of_hom_pos
    {R : Type u} [Field R]
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : RatFunc R →+* K) {b c : RatFunc R}
    (hb : 0 < f b) (hc : 0 < f c) :
    NormalizedOrderingObstruction b c := by
  let P : _root_.RingPreordering (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.comapNonnegative f
  exact ⟨P, inferInstance,
    (strictPos_comapNonnegative_of_pos f hb).mem,
    (strictPos_comapNonnegative_of_pos f hb).neg_notMem,
    (strictPos_comapNonnegative_of_pos f hc).mem,
    (strictPos_comapNonnegative_of_pos f hc).neg_notMem⟩

theorem normalizedOrderingObstruction_iff_strictPos
    {R : Type u} [Field R] {b c : RatFunc R} :
    NormalizedOrderingObstruction b c ↔
      ∃ P : _root_.RingPreordering (RatFunc R),
        P.IsOrdering ∧
          RatFuncWittLocalGlobal.RingPreordering.StrictPos P b ∧
          RatFuncWittLocalGlobal.RingPreordering.StrictPos P c := by
  constructor
  · rintro ⟨P, hP, hb, hnb, hc, hnc⟩
    exact ⟨P, hP, ⟨hb, hnb⟩, ⟨hc, hnc⟩⟩
  · rintro ⟨P, hP, hb, hc⟩
    exact ⟨P, hP, hb.mem, hb.neg_notMem, hc.mem, hc.neg_notMem⟩

theorem normalizedOrderingObstruction_of_ordered_pos
    {R : Type u} [Field R] [LinearOrder (RatFunc R)] [IsStrictOrderedRing (RatFunc R)]
    {b c : RatFunc R} (hb : 0 < b) (hc : 0 < c) :
    NormalizedOrderingObstruction b c := by
  let P : _root_.RingPreordering (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.nonnegative (RatFunc R)
  refine ⟨P, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact le_of_lt hb
  · intro hnb
    change 0 ≤ -b at hnb
    have hb_nonpos : b ≤ 0 := by
      exact neg_nonneg.mp hnb
    exact (not_le_of_gt hb) hb_nonpos
  · exact le_of_lt hc
  · intro hnc
    change 0 ≤ -c at hnc
    have hc_nonpos : c ≤ 0 := by
      exact neg_nonneg.mp hnc
    exact (not_le_of_gt hc) hc_nonpos

theorem normalizedOrderingObstruction_of_orderedRatFuncPositivePair
    {R : Type u} [Field R] {b c : RatFunc R}
    (h : OrderedRatFuncPositivePair b c) :
    NormalizedOrderingObstruction b c := by
  let _ := h.linearOrder
  let _ := h.strictOrdered
  exact normalizedOrderingObstruction_of_ordered_pos h.pos_left h.pos_right

theorem orderedRatFuncPositivePair_of_normalizedOrderingObstruction
    {R : Type u} [Field R] {b c : RatFunc R}
    (h : NormalizedOrderingObstruction b c) :
    Nonempty (OrderedRatFuncPositivePair b c) := by
  classical
  rw [normalizedOrderingObstruction_iff_strictPos] at h
  rcases h with ⟨P, hP, hb, hc⟩
  let _ : P.IsOrdering := hP
  let _ : LinearOrder (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.linearOrderOfIsOrdering P
  let _ : IsStrictOrderedRing (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.isStrictOrderedRingOfIsOrdering P
  exact ⟨{
    pos_left :=
      (RatFuncWittLocalGlobal.RingPreordering.strictPos_iff_zero_lt_linearOrderOfIsOrdering
        P).mp hb
    pos_right :=
      (RatFuncWittLocalGlobal.RingPreordering.strictPos_iff_zero_lt_linearOrderOfIsOrdering
        P).mp hc
  }⟩

theorem normalizedOrderingObstruction_of_sameStrictSign_factors
    {R : Type u} [Field R] {g b₁ c₁ b c : RatFunc R}
    (hb : b = g * b₁) (hc : c = g * c₁) :
    SameStrictSignOrdering g b₁ c₁ → NormalizedOrderingObstruction b c := by
  rintro ⟨P, hP, hsame⟩
  have _ : P.IsOrdering := hP
  apply normalizedOrderingObstruction_iff_strictPos.mpr
  rcases hsame with hpos | hneg
  · rcases hpos with ⟨hg, hb₁, hc₁⟩
    exact ⟨P, hP, by simpa [hb] using hg.mul hb₁, by simpa [hc] using hg.mul hc₁⟩
  · rcases hneg with ⟨hg, hb₁, hc₁⟩
    exact ⟨P, hP, by simpa [hb] using hg.mul hb₁, by simpa [hc] using hg.mul hc₁⟩

theorem normalizedOrderingObstruction_of_sameStrictSign_div
    {R : Type u} [Field R] {a b c : RatFunc R} :
    SameStrictSignOrdering a b c →
      NormalizedOrderingObstruction (b / a) (c / a) := by
  rintro ⟨P, hP, hsame⟩
  have _ : P.IsOrdering := hP
  let _ : LinearOrder (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.linearOrderOfIsOrdering P
  let _ : IsStrictOrderedRing (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.isStrictOrderedRingOfIsOrdering P
  rcases hsame with hpos | hneg
  · rcases hpos with ⟨haP, hbP, hcP⟩
    have ha_pos : 0 < a :=
      (RatFuncWittLocalGlobal.RingPreordering.strictPos_iff_zero_lt_linearOrderOfIsOrdering
        P).mp haP
    have hb_pos : 0 < b :=
      (RatFuncWittLocalGlobal.RingPreordering.strictPos_iff_zero_lt_linearOrderOfIsOrdering
        P).mp hbP
    have hc_pos : 0 < c :=
      (RatFuncWittLocalGlobal.RingPreordering.strictPos_iff_zero_lt_linearOrderOfIsOrdering
        P).mp hcP
    exact normalizedOrderingObstruction_of_ordered_pos
      (div_pos hb_pos ha_pos) (div_pos hc_pos ha_pos)
  · rcases hneg with ⟨haP, hbP, hcP⟩
    have ha_neg : a < 0 := neg_pos.mp
      ((RatFuncWittLocalGlobal.RingPreordering.strictPos_iff_zero_lt_linearOrderOfIsOrdering
        P).mp haP)
    have hb_neg : b < 0 := neg_pos.mp
      ((RatFuncWittLocalGlobal.RingPreordering.strictPos_iff_zero_lt_linearOrderOfIsOrdering
        P).mp hbP)
    have hc_neg : c < 0 := neg_pos.mp
      ((RatFuncWittLocalGlobal.RingPreordering.strictPos_iff_zero_lt_linearOrderOfIsOrdering
        P).mp hcP)
    exact normalizedOrderingObstruction_of_ordered_pos
      (div_pos_of_neg_of_neg hb_neg ha_neg)
      (div_pos_of_neg_of_neg hc_neg ha_neg)

/--
Abstract Artin-Schreier real-closure input: every ordered field embeds
order-preservingly into a real closed ordered field.

Mathlib does not currently expose a general real-closure construction for an
arbitrary ordered field, so the project keeps this as the precise global
real-closure principle needed by `NormalizedOrderingRealization`.
-/
def OrderedFieldRealClosedExtension : Prop :=
  ∀ (F : Type u) [Field F] [LinearOrder F] [IsStrictOrderedRing F],
    ∃ (K : Type v), ∃ (_ : Field K), ∃ (_ : LinearOrder K),
      ∃ (_ : IsStrictOrderedRing K), ∃ (_ : IsRealClosed K), ∃ (_ : Algebra F K),
        ∀ x : F, 0 < x → 0 < algebraMap F K x

/--
The narrower real-closure input actually used in this project: every ordered
field structure on `RatFunc R` embeds order-preservingly into a real closed
ordered field.
-/
def RatFuncOrderedRealClosedExtension
    (R : Type u) [Field R] : Prop :=
  ∀ (_ : LinearOrder (RatFunc R)) (_ : IsStrictOrderedRing (RatFunc R)),
    ∃ (K : Type v), ∃ (_ : Field K), ∃ (_ : LinearOrder K),
      ∃ (_ : IsStrictOrderedRing K), ∃ (_ : IsRealClosed K),
        ∃ (_ : Algebra (RatFunc R) K),
          ∀ x : RatFunc R, 0 < x → 0 < algebraMap (RatFunc R) K x

theorem ratFuncOrderedRealClosedExtension_of_orderedFieldRealClosedExtension
    {R : Type u} [Field R]
    (hclosure : OrderedFieldRealClosedExtension.{u, v}) :
    RatFuncOrderedRealClosedExtension.{u, v} R := by
  intro horder hstrict
  let _ : LinearOrder (RatFunc R) := horder
  let _ : IsStrictOrderedRing (RatFunc R) := hstrict
  exact hclosure (RatFunc R)

/--
Realization principle for ordering obstructions: every ordering of `RatFunc R`
where both coefficients are positive is realized in some real closed target.
This is the order-theoretic gap between the current abstract obstruction and a
concrete real-place obstruction.
-/
def NormalizedOrderingRealization
    (R : Type u) [Field R] : Prop :=
  ∀ b c : RatFunc R,
    NormalizedOrderingObstruction b c →
      HasNormalizedSignObstruction.{u, v} b c

theorem hasNormalizedSignObstruction_of_orderedRatFuncPositivePair_ratFuncClosure
    {R : Type u} [Field R]
    (hclosure : RatFuncOrderedRealClosedExtension.{u, v} R) {b c : RatFunc R}
    (hpair : OrderedRatFuncPositivePair b c) :
    HasNormalizedSignObstruction.{u, v} b c := by
  let _ := hpair.linearOrder
  let _ := hpair.strictOrdered
  rcases hclosure inferInstance inferInstance with
    ⟨K, hKfield, hKorder, hKstrict, hKrealClosed, hKalg, hpos⟩
  let _ : Field K := hKfield
  let _ : LinearOrder K := hKorder
  let _ : IsStrictOrderedRing K := hKstrict
  let _ : IsRealClosed K := hKrealClosed
  let _ : Algebra (RatFunc R) K := hKalg
  exact ⟨{
    K := K
    pos_left := hpos b hpair.pos_left
    pos_right := hpos c hpair.pos_right
  }⟩

theorem normalizedOrderingRealization_of_ratFuncOrderedRealClosedExtension
    {R : Type u} [Field R]
    (hclosure : RatFuncOrderedRealClosedExtension.{u, v} R) :
    NormalizedOrderingRealization.{u, v} R := by
  intro b c h
  rcases orderedRatFuncPositivePair_of_normalizedOrderingObstruction h with ⟨hpair⟩
  exact hasNormalizedSignObstruction_of_orderedRatFuncPositivePair_ratFuncClosure hclosure hpair

theorem normalizedOrderingRealization_of_orderedFieldRealClosedExtension
    {R : Type u} [Field R]
    (hclosure : OrderedFieldRealClosedExtension.{u, v}) :
    NormalizedOrderingRealization.{u, v} R :=
  normalizedOrderingRealization_of_ratFuncOrderedRealClosedExtension
    (ratFuncOrderedRealClosedExtension_of_orderedFieldRealClosedExtension hclosure)

theorem not_finiteSameStrictSignOrdering_of_forall_realClosedExtension_ratFuncClosure
    {R : Type u} [Field R] {ι : Type w} [Fintype ι]
    (hclosure : RatFuncOrderedRealClosedExtension.{u, v} R)
    (a : ι → RatFunc R)
    (hlocal :
      ∀ {K : Type v}
        [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
        [Algebra (RatFunc R) K],
        ∃ x : ι → K,
          x ≠ 0 ∧
            ∑ i, algebraMap (RatFunc R) K (a i) * x i ^ 2 = 0) :
    ¬ FiniteSameStrictSignOrdering a := by
  rintro ⟨P, hP, hsign⟩
  have _ : P.IsOrdering := hP
  let _ : LinearOrder (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.linearOrderOfIsOrdering P
  let _ : IsStrictOrderedRing (RatFunc R) :=
    RatFuncWittLocalGlobal.RingPreordering.isStrictOrderedRingOfIsOrdering P
  rcases hclosure inferInstance inferInstance with
    ⟨K, hKfield, hKorder, hKstrict, hKrealClosed, hKalg, hpos⟩
  let _ : Field K := hKfield
  let _ : LinearOrder K := hKorder
  let _ : IsStrictOrderedRing K := hKstrict
  let _ : IsRealClosed K := hKrealClosed
  let _ : Algebra (RatFunc R) K := hKalg
  rcases hlocal (K := K) with ⟨x, hx_ne, hx_sum⟩
  have hiso : Diagonal.Isotropic (fun i => algebraMap (RatFunc R) K (a i)) :=
    ⟨x, hx_ne, hx_sum⟩
  rcases hsign with hposP | hnegP
  · have hall_pos : ∀ i, 0 < algebraMap (RatFunc R) K (a i) := by
      intro i
      exact hpos (a i)
        ((RatFuncWittLocalGlobal.RingPreordering.strictPos_iff_zero_lt_linearOrderOfIsOrdering
          P).mp (hposP i))
    exact (Diagonal.not_isotropic_of_all_pos hall_pos) hiso
  · have hall_neg : ∀ i, algebraMap (RatFunc R) K (a i) < 0 := by
      intro i
      have hneg_img : 0 < algebraMap (RatFunc R) K (-(a i)) :=
        hpos (-(a i))
          ((RatFuncWittLocalGlobal.RingPreordering.strictPos_iff_zero_lt_linearOrderOfIsOrdering
            P).mp (hnegP i))
      simpa using neg_pos.mp (by simpa using hneg_img)
    exact (Diagonal.not_isotropic_of_all_neg hall_neg) hiso

theorem not_finiteSameStrictSignOrdering_of_forall_realClosedExtension
    {R : Type u} [Field R] {ι : Type w} [Fintype ι]
    (hclosure : OrderedFieldRealClosedExtension.{u, v})
    (a : ι → RatFunc R)
    (hlocal :
      ∀ {K : Type v}
        [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
        [Algebra (RatFunc R) K],
        ∃ x : ι → K,
          x ≠ 0 ∧
            ∑ i, algebraMap (RatFunc R) K (a i) * x i ^ 2 = 0) :
    ¬ FiniteSameStrictSignOrdering a :=
  not_finiteSameStrictSignOrdering_of_forall_realClosedExtension_ratFuncClosure
    (ratFuncOrderedRealClosedExtension_of_orderedFieldRealClosedExtension hclosure)
    a hlocal

theorem forall_realClosedExtension_of_not_finiteSameStrictSignOrdering
    {R : Type u} [Field R] {ι : Type w} [Fintype ι] [Nonempty ι]
    (a : ι → RatFunc R)
    (hreg : ∀ i, a i ≠ 0)
    (hno : ¬ FiniteSameStrictSignOrdering a) :
    ∀ {K : Type v}
      [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
      [Algebra (RatFunc R) K],
      ∃ x : ι → K,
        x ≠ 0 ∧
          ∑ i, algebraMap (RatFunc R) K (a i) * x i ^ 2 = 0 := by
  intro K _ _ _ _ _
  by_contra hnot
  have haniso :
      ¬ Diagonal.Isotropic (fun i => algebraMap (RatFunc R) K (a i)) := by
    rintro ⟨x, hx_ne, hx_sum⟩
    exact hnot ⟨x, hx_ne, hx_sum⟩
  exact hno
    (finiteSameStrictSignOrdering_of_hom_not_isotropic
      (algebraMap (RatFunc R) K) hreg haniso)

theorem forall_realClosedExtension_iff_not_finiteSameStrictSignOrdering_ratFuncClosure
    {R : Type u} [Field R] {ι : Type w} [Fintype ι] [Nonempty ι]
    (hclosure : RatFuncOrderedRealClosedExtension.{u, v} R)
    (a : ι → RatFunc R)
    (hreg : ∀ i, a i ≠ 0) :
    (∀ {K : Type v}
      [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
      [Algebra (RatFunc R) K],
      ∃ x : ι → K,
        x ≠ 0 ∧
          ∑ i, algebraMap (RatFunc R) K (a i) * x i ^ 2 = 0) ↔
      ¬ FiniteSameStrictSignOrdering a := by
  constructor
  · exact not_finiteSameStrictSignOrdering_of_forall_realClosedExtension_ratFuncClosure hclosure a
  · exact forall_realClosedExtension_of_not_finiteSameStrictSignOrdering a hreg

theorem forall_realClosedExtension_iff_not_finiteSameStrictSignOrdering
    {R : Type u} [Field R] {ι : Type w} [Fintype ι] [Nonempty ι]
    (hclosure : OrderedFieldRealClosedExtension.{u, v})
    (a : ι → RatFunc R)
    (hreg : ∀ i, a i ≠ 0) :
    (∀ {K : Type v}
      [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
      [Algebra (RatFunc R) K],
      ∃ x : ι → K,
        x ≠ 0 ∧
          ∑ i, algebraMap (RatFunc R) K (a i) * x i ^ 2 = 0) ↔
      ¬ FiniteSameStrictSignOrdering a :=
  forall_realClosedExtension_iff_not_finiteSameStrictSignOrdering_ratFuncClosure
    (ratFuncOrderedRealClosedExtension_of_orderedFieldRealClosedExtension hclosure)
    a hreg

theorem normalizedOrderingObstruction_swap
    {R : Type u} [Field R] {b c : RatFunc R} :
    NormalizedOrderingObstruction b c ↔
      NormalizedOrderingObstruction c b := by
  constructor
  · rintro ⟨P, hP, hb, hnb, hc, hnc⟩
    exact ⟨P, hP, hc, hnc, hb, hnb⟩
  · rintro ⟨P, hP, hc, hnc, hb, hnb⟩
    exact ⟨P, hP, hb, hnb, hc, hnc⟩

theorem normalizedSignObstructionFree_iff_not_hasObstruction
    {R : Type u} [Field R] (b c : RatFunc R) :
    NormalizedSignObstructionFree.{u, v} b c ↔
      ¬ HasNormalizedSignObstruction.{u, v} b c := by
  constructor
  · intro hfree hbad
    rcases hbad with ⟨w⟩
    let _ := w.field
    let _ := w.linearOrder
    let _ := w.strictOrdered
    let _ := w.realClosed
    let _ := w.algebra
    rcases hfree (K := w.K) with hb | hc
    · exact (not_le_of_gt w.pos_left) hb
    · exact (not_le_of_gt w.pos_right) hc
  · intro hno K _ _ _ _ _
    by_contra hsign
    rw [not_or] at hsign
    exact hno ⟨{
      K := K
      pos_left := not_le.mp hsign.1
      pos_right := not_le.mp hsign.2
    }⟩

theorem hasNormalizedSignObstruction_mul_square
    {R : Type u} [Field R] {b c r s : RatFunc R}
    (hr : r ≠ 0) (hs : s ≠ 0) :
    HasNormalizedSignObstruction.{u, v} (b * r ^ 2) (c * s ^ 2) ↔
      HasNormalizedSignObstruction.{u, v} b c := by
  constructor
  · rintro ⟨w⟩
    let _ := w.field
    let _ := w.linearOrder
    let _ := w.strictOrdered
    let _ := w.realClosed
    let _ := w.algebra
    have hrK : algebraMap (RatFunc R) w.K r ≠ 0 :=
      by simpa using (algebraMap (RatFunc R) w.K).injective.ne hr
    have hsK : algebraMap (RatFunc R) w.K s ≠ 0 :=
      by simpa using (algebraMap (RatFunc R) w.K).injective.ne hs
    exact ⟨{
      K := w.K
      pos_left := pos_of_mul_pos_left
        (by simpa [map_mul, map_pow] using w.pos_left)
        (sq_nonneg (algebraMap (RatFunc R) w.K r))
      pos_right := pos_of_mul_pos_left
        (by simpa [map_mul, map_pow] using w.pos_right)
        (sq_nonneg (algebraMap (RatFunc R) w.K s))
    }⟩
  · rintro ⟨w⟩
    let _ := w.field
    let _ := w.linearOrder
    let _ := w.strictOrdered
    let _ := w.realClosed
    let _ := w.algebra
    have hrK : algebraMap (RatFunc R) w.K r ≠ 0 :=
      by simpa using (algebraMap (RatFunc R) w.K).injective.ne hr
    have hsK : algebraMap (RatFunc R) w.K s ≠ 0 :=
      by simpa using (algebraMap (RatFunc R) w.K).injective.ne hs
    exact ⟨{
      K := w.K
      pos_left := by
        simpa [map_mul, map_pow] using
          mul_pos w.pos_left (sq_pos_of_ne_zero hrK)
      pos_right := by
        simpa [map_mul, map_pow] using
          mul_pos w.pos_right (sq_pos_of_ne_zero hsK)
    }⟩

theorem hasNormalizedSignObstruction_polynomial_mul_square
    {R : Type u} [Field R] {B C S T : Polynomial R}
    (hS : S ≠ 0) (hT : T ≠ 0) :
    HasNormalizedSignObstruction.{u, v}
        (algebraMap (Polynomial R) (RatFunc R) (B * S ^ 2))
        (algebraMap (Polynomial R) (RatFunc R) (C * T ^ 2)) ↔
      HasNormalizedSignObstruction.{u, v}
        (algebraMap (Polynomial R) (RatFunc R) B)
        (algebraMap (Polynomial R) (RatFunc R) C) := by
  let s : RatFunc R := algebraMap (Polynomial R) (RatFunc R) S
  let t : RatFunc R := algebraMap (Polynomial R) (RatFunc R) T
  have hs : s ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hS
  have ht : t ≠ 0 := _root_.RatFunc.algebraMap_ne_zero hT
  simpa [s, t, map_mul, map_pow] using
    (hasNormalizedSignObstruction_mul_square (R := R)
      (b := algebraMap (Polynomial R) (RatFunc R) B)
      (c := algebraMap (Polynomial R) (RatFunc R) C)
      (r := s) (s := t) hs ht)

theorem normalizedSignObstructionFree_iff_locallyIsotropic
    {R : Type u} [Field R] (b c : RatFunc R) :
    NormalizedSignObstructionFree.{u, v} b c ↔
      TernaryLocallyIsotropic.{u, v} 1 b c := by
  constructor
  · intro h K _ _ _ _ _
    have hsign := h (K := K)
    simpa using
      (Diagonal.ternary_isotropic_one_iff
        (algebraMap (RatFunc R) K b)
        (algebraMap (RatFunc R) K c)).mpr hsign
  · intro h K _ _ _ _ _
    have hloc := h (K := K)
    have hloc' :
        Diagonal.TernaryIsotropic 1
          (algebraMap (RatFunc R) K b)
          (algebraMap (RatFunc R) K c) := by
      simpa using hloc
    simpa using
      (Diagonal.ternary_isotropic_one_iff
        (algebraMap (RatFunc R) K b)
        (algebraMap (RatFunc R) K c)).mp hloc'

theorem normalizedSignObstructionFree_mul_square
    {R : Type u} [Field R] {b c u v : RatFunc R}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    NormalizedSignObstructionFree.{u, v} (b * u ^ 2) (c * v ^ 2) ↔
      NormalizedSignObstructionFree.{u, v} b c := by
  constructor
  · intro h K _ _ _ _ _
    have hsign := h (K := K)
    have huK : algebraMap (RatFunc R) K u ≠ 0 :=
      by simpa using (algebraMap (RatFunc R) K).injective.ne hu
    have hvK : algebraMap (RatFunc R) K v ≠ 0 :=
      by simpa using (algebraMap (RatFunc R) K).injective.ne hv
    rcases hsign with hb | hc
    · left
      exact nonpos_of_mul_nonpos_left (by simpa [map_mul, map_pow] using hb)
        (sq_pos_of_ne_zero huK)
    · right
      exact nonpos_of_mul_nonpos_left (by simpa [map_mul, map_pow] using hc)
        (sq_pos_of_ne_zero hvK)
  · intro h K _ _ _ _ _
    have hsign := h (K := K)
    rcases hsign with hb | hc
    · left
      simpa [map_mul, map_pow] using
        (mul_nonpos_of_nonpos_of_nonneg
          (by simpa using hb)
          (sq_nonneg (algebraMap (RatFunc R) K u)))
    · right
      simpa [map_mul, map_pow] using
        (mul_nonpos_of_nonpos_of_nonneg
          (by simpa using hc)
          (sq_nonneg (algebraMap (RatFunc R) K v)))

end RatFunc
end RatFuncWittLocalGlobal
