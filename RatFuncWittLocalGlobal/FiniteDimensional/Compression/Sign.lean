/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.FiniteDimensional.ScalarSign
import RatFuncWittLocalGlobal.Sign.Strict

/-!
# Sign rule for binary-tail compression

A binary head and any nonempty finite tail are compressed by one coefficient
whose sign makes both resulting blocks nondefinite.
-/

namespace RatFuncWittLocalGlobal

universe u

noncomputable section

/-- Required sign for compressing a binary head against a finite tail. -/
def binaryTailCompressionRequiredSign
    {F κ : Type*} [LinearOrder F] [Zero F]
    (head : Fin 2 → F) (tail : κ → F) : StrictSign := by
  classical
  exact if (∀ i, 0 < head i) ∨ (∀ j, tail j < 0) then .neg else .pos

/-- Componentwise preservation of nonzero strict signs preserves the
binary-tail compression sign, even when the two families live in different
ordered fields. -/
theorem binaryTailCompressionRequiredSign_eq_of_pos_iff
    {F K κ : Type*}
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (headF : Fin 2 → F) (tailF : κ → F)
    (headK : Fin 2 → K) (tailK : κ → K)
    (htailF : ∀ j, tailF j ≠ 0) (htailK : ∀ j, tailK j ≠ 0)
    (hheadPos : ∀ i, 0 < headF i ↔ 0 < headK i)
    (htailPos : ∀ j, 0 < tailF j ↔ 0 < tailK j) :
    binaryTailCompressionRequiredSign headF tailF =
      binaryTailCompressionRequiredSign headK tailK := by
  have htailNeg (j : κ) : tailF j < 0 ↔ tailK j < 0 := by
    constructor
    · intro hj
      have hnot : ¬ 0 < tailK j := fun hk =>
        (not_lt_of_ge hj.le) ((htailPos j).mpr hk)
      exact lt_of_le_of_ne (le_of_not_gt hnot) (htailK j)
    · intro hj
      have hnot : ¬ 0 < tailF j := fun hf =>
        (not_lt_of_ge hj.le) ((htailPos j).mp hf)
      exact lt_of_le_of_ne (le_of_not_gt hnot) (htailF j)
  simp only [binaryTailCompressionRequiredSign]
  congr 1
  simp only [hheadPos, htailNeg]

/-- The binary-tail sign rule prevents both the ternary head and the tail
enlarged by the negative compression coefficient from being definite. -/
theorem binaryTailCompressionRequiredSign_spec
    {F κ : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Nonempty κ]
    (head : Fin 2 → F) (tail : κ → F)
    (hno : ¬ ScalarFamilySameStrictSign (Sum.elim head tail))
    {s : F} (hs : (binaryTailCompressionRequiredSign head tail).Holds s) :
    ¬ ScalarFamilySameStrictSign (![head 0, head 1, s] : Fin 3 → F) ∧
      ¬ ScalarFamilySameStrictSign
        (Sum.elim tail (fun _ : Fin 1 => -s)) := by
  have hheadPos : (∀ i, 0 < head i) → s < 0 := by
    intro h
    simpa [binaryTailCompressionRequiredSign, h, StrictSign.Holds] using hs
  have htailNeg : (∀ j, tail j < 0) → s < 0 := by
    intro h
    simpa [binaryTailCompressionRequiredSign, h, StrictSign.Holds] using hs
  have hheadNeg : (∀ i, head i < 0) → 0 < s := by
    intro h
    have hnotTail : ¬ ∀ j, tail j < 0 := by
      intro htail
      apply hno
      right
      intro i
      cases i with
      | inl i => exact h i
      | inr j => exact htail j
    have hnotHeadPos : ¬ ∀ i, 0 < head i := by
      intro hpos
      exact (not_lt_of_ge (hpos 0).le) (h 0)
    simpa [binaryTailCompressionRequiredSign, hnotHeadPos, hnotTail,
      StrictSign.Holds] using hs
  have htailPos : (∀ j, 0 < tail j) → 0 < s := by
    intro h
    have hnotHead : ¬ ∀ i, 0 < head i := by
      intro hhead
      apply hno
      left
      intro i
      cases i with
      | inl i => exact hhead i
      | inr j => exact h j
    have hnotTailNeg : ¬ ∀ j, tail j < 0 := by
      intro hneg
      let j : κ := Classical.choice inferInstance
      exact (not_lt_of_ge (h j).le) (hneg j)
    simpa [binaryTailCompressionRequiredSign, hnotHead, hnotTailNeg,
      StrictSign.Holds] using hs
  constructor
  · rintro (hpos | hneg)
    · have hspos : 0 < s := by simpa using hpos 2
      exact (not_lt_of_ge hspos.le)
        (hheadPos (fun i => by
          fin_cases i
          · simpa using hpos 0
          · simpa using hpos 1))
    · have hsneg : s < 0 := by simpa using hneg 2
      exact (not_lt_of_ge
        (hheadNeg (fun i => by
          fin_cases i
          · simpa using hneg 0
          · simpa using hneg 1)).le) hsneg
  · rintro (hpos | hneg)
    · have hsneg : s < 0 := by simpa using hpos (Sum.inr 0)
      exact (not_lt_of_ge (htailPos (fun j => hpos (Sum.inl j))).le) hsneg
    · have hspos : 0 < s := by simpa using hneg (Sum.inr 0)
      exact (not_lt_of_ge hspos.le) (htailNeg (fun j => hneg (Sum.inl j)))

end

end RatFuncWittLocalGlobal
