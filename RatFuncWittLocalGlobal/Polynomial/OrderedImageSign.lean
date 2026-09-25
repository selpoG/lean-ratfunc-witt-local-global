/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Polynomial.OrderedExtensionSign

/-!
# Signs under ordered images of a rational-function field

This module records the field-homomorphism facts needed to transport
polynomial signs through finite cuts in ordered extensions.
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u v

/-- A field homomorphism from a real closed ordered field to an ordered field
necessarily preserves the strict order. -/
theorem realClosed_ringHom_strictMono
    {R : Type u} {K : Type v}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (φ : R →+* K) : StrictMono φ := by
  rw [strictMono_iff_map_pos]
  intro a ha
  rcases IsSquare.of_nonneg ha.le with ⟨b, rfl⟩
  have hb : b ≠ 0 := by
    intro hb
    simp [hb] at ha
  have hφb : φ b ≠ 0 := by
    intro hz
    exact hb (RingHom.injective φ (by simpa using hz))
  simpa using mul_self_pos.mpr hφb

/-- The image of the rational-function variable cannot equal the image of a
base-field constant under a field homomorphism. -/
theorem ratFunc_X_image_ne_base
    {R : Type u} {K : Type v} [Field R] [Field K]
    (f : _root_.RatFunc R →+* K) (r : R) :
    f _root_.RatFunc.X ≠ f (algebraMap R (_root_.RatFunc R) r) := by
  intro h
  have hz :
      f (algebraMap (Polynomial R) (_root_.RatFunc R) (X - C r)) = 0 := by
    simpa [map_sub] using sub_eq_zero.mpr h
  have hz' : algebraMap (Polynomial R) (_root_.RatFunc R) (X - C r) = 0 :=
    RingHom.injective f (by simpa using hz)
  have hp : (X - C r : Polynomial R) = 0 :=
    FaithfulSMul.algebraMap_injective (Polynomial R) (_root_.RatFunc R)
      (by simpa using hz')
  exact Polynomial.X_sub_C_ne_zero r hp

end RatFuncWittLocalGlobal
