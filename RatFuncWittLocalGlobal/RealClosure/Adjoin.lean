/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.RealClosure.Intermediate
import Mathlib.Algebra.Order.Algebra

/-!
# Ordered subfield bridges for the ambient algebraic closure

This file packages the elementary bridge from an ordered intermediate field
`E` to an ordered intermediate subfield `L` of the ambient algebraic closure.
The order on `L` is carried by its usual `LinearOrder`; the only compatibility
needed is that the scalar extension `E.carrier → L` is order preserving.  For
ordered fields this already reflects nonnegativity, since the algebra map is
injective.
-/

namespace RatFuncWittLocalGlobal
namespace OrderedRealClosure

universe u

open Polynomial

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

local notation "Ω" => AlgebraicClosure F

@[simp] theorem Intermediate.zero_le_iff_ambient_nonnegative (E : Intermediate F)
    {x : E.carrier} :
    0 ≤ x ↔ (x : Ω) ∈ E.nonnegative := by
  calc
    0 ≤ x ↔ x ∈ ambientConePreordering E := by
      exact RingPreordering.zero_le_linearOrderOfIsOrdering_iff
        (ambientConePreordering E)
    _ ↔ (x : Ω) ∈ E.nonnegative := mem_ambientConePreordering (E := E)

/-!
### Ordered algebra maps

`IsOrderedModule` gives monotonicity of an algebra map.  For a field
extension, injectivity upgrades monotonicity to strict monotonicity, hence the
map reflects the nonnegative cone as well.
-/

theorem algebraMap_nonneg_iff_of_isOrderedModule
    {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [Algebra K L]
    [IsOrderedModule K L] {x : K} :
    0 ≤ algebraMap K L x ↔ 0 ≤ x := by
  have hmono : Monotone (algebraMap K L) := algebraMap_mono L
  have hstrict : StrictMono (algebraMap K L) :=
    hmono.strictMono_of_injective (RingHom.injective (algebraMap K L))
  simpa using (hstrict.le_iff_le (a := (0 : K)) (b := x))

private def orderedSubfieldCone (E : Intermediate F) (L : IntermediateField E.carrier Ω)
    [LinearOrder L] : Set Ω :=
  {x | ∃ y : L, 0 ≤ y ∧ (y : Ω) = x}

omit [IsStrictOrderedRing F] in
noncomputable def Intermediate.ofOrderedSubfield
    (E : Intermediate F) (L : IntermediateField E.carrier Ω)
    [LinearOrder L] [IsStrictOrderedRing L] [IsOrderedModule E.carrier L] :
    Intermediate F := by
  let U : IntermediateField F Ω := IntermediateField.restrictScalars F L
  let C : Set Ω := orderedSubfieldCone E L
  refine
    { carrier := U
      nonnegative := C
      nonnegative_subset := ?_
      zero_mem := ?_
      one_mem := ?_
      add_mem := ?_
      mul_mem := ?_
      square_mem := ?_
      total := ?_
      proper := ?_
      base_nonnegative := ?_ }
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    change (y : Ω) ∈ U
    exact y.property
  · exact ⟨0, le_rfl, by simp⟩
  · exact ⟨1, zero_le_one, by simp⟩
  · rintro x y ⟨x', hx', rfl⟩ ⟨y', hy', rfl⟩
    refine ⟨x' + y', add_nonneg hx' hy', ?_⟩
    simp
  · rintro x y ⟨x', hx', rfl⟩ ⟨y', hy', rfl⟩
    refine ⟨x' * y', mul_nonneg hx' hy', ?_⟩
    simp
  · intro x hx
    change x ∈ U at hx
    let x' : L := ⟨x, hx⟩
    exact ⟨x' ^ 2, sq_nonneg x', rfl⟩
  · intro x hx
    change x ∈ U at hx
    let x' : L := ⟨x, hx⟩
    rcases le_total 0 x' with hx' | hx'
    · exact Or.inl ⟨x', hx', rfl⟩
    · exact Or.inr ⟨-x', neg_nonneg.mpr hx', rfl⟩
  · rintro ⟨x, hx, hxeq⟩
    have hxneg : x = (-1 : L) := by
      apply Subtype.ext
      simpa using hxeq
    subst hxneg
    norm_num at hx
  · intro x
    constructor
    · intro hx
      have hxE : 0 ≤ algebraMap F E.carrier x :=
        (base_nonnegative_iff (F := F) E x).mp hx
      have hxL : 0 ≤ algebraMap E.carrier L (algebraMap F E.carrier x) :=
        algebraMap_nonneg L hxE
      refine ⟨algebraMap F L x, ?_, ?_⟩
      · simpa [IsScalarTower.algebraMap_apply F E.carrier L x] using hxL
      · simp [IsScalarTower.algebraMap_apply F E.carrier L x]
    · rintro ⟨y, hy, hxy⟩
      have hy' : y = algebraMap F L x := by
        apply Subtype.ext
        simpa [IsScalarTower.algebraMap_apply F E.carrier L x] using hxy
      subst hy'
      have hxL : 0 ≤ algebraMap F L x := hy
      have hxE : 0 ≤ algebraMap F E.carrier x :=
        (algebraMap_nonneg_iff_of_isOrderedModule
          (K := E.carrier) (L := L)).mp (by
            simpa [IsScalarTower.algebraMap_apply F E.carrier L x] using hxL)
      exact (base_nonnegative_iff (F := F) E x).mpr hxE

theorem Intermediate.le_ofOrderedSubfield
    (E : Intermediate F) (L : IntermediateField E.carrier Ω)
    [LinearOrder L] [IsStrictOrderedRing L] [IsOrderedModule E.carrier L] :
    E ≤ E.ofOrderedSubfield L := by
  let hcarrier : E.carrier ≤ IntermediateField.restrictScalars F L := by
    intro x hx
    change x ∈ L
    simpa using L.algebraMap_mem (⟨x, hx⟩ : E.carrier)
  refine ⟨hcarrier, ?_⟩
  intro x hx
  constructor
  · intro h
    let xE : E.carrier := ⟨x, hx⟩
    refine ⟨algebraMap E.carrier L xE, ?_, ?_⟩
    · exact algebraMap_nonneg L
        ((Intermediate.zero_le_iff_ambient_nonnegative (F := F) E).mpr h)
    · change (x : Ω) = x
      rfl
  · rintro ⟨y, hy, hxy⟩
    let xE : E.carrier := ⟨x, hx⟩
    have hyx : algebraMap E.carrier L xE = y := by
      apply Subtype.ext
      simpa using hxy.symm
    have hxE : 0 ≤ xE := by
      apply (algebraMap_nonneg_iff_of_isOrderedModule
        (K := E.carrier) (L := L)).mp
      simpa [hyx] using hy
    exact (Intermediate.zero_le_iff_ambient_nonnegative (F := F) E).mp hxE

end OrderedRealClosure
end RatFuncWittLocalGlobal
