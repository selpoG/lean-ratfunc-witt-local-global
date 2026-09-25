/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.RealClosure.Odd.Proper
import RatFuncWittLocalGlobal.RealClosure.Adjoin

/-!
# Odd roots in a maximal ordered intermediate field

An odd polynomial over a maximal ordered intermediate field has a root in
that field.  The root is first adjoined in the ambient algebraic closure;
the odd power-basis ordering witness makes this a compatible ordered
extension, so maximality brings the adjoined root back down.
-/

namespace RatFuncWittLocalGlobal

open scoped _root_.Polynomial
open _root_.Polynomial

namespace OrderedRealClosure

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

local notation "Ω" => AlgebraicClosure F

/-!
### The odd simple-adjunction ordering bridge
-/

theorem exists_ordered_odd_adjoin
    (M : Intermediate F) {q : M.carrier[X]} {α : Ω}
    (hqodd : Odd q.natDegree) (hqmonic : q.Monic) (hqirr : Irreducible q)
    (hroot : Polynomial.aeval α q = 0) :
    ∃ (L : IntermediateField M.carrier Ω)
      (pb : PowerBasis M.carrier L)
      (O : RingPreordering L) (hO : O.IsOrdering),
      L = IntermediateField.adjoin M.carrier ({α} : Set Ω) ∧
        pb.dim = q.natDegree ∧ Odd pb.dim ∧
        (pb.gen : Ω) = α ∧
        (∀ a : M.carrier, 0 ≤ a →
          @LE.le L
            (@RingPreordering.linearOrderOfIsOrdering L _ O hO).toLE
            0 (algebraMap M.carrier L a)) ∧
        (∀ a : M.carrier, 0 < a →
          @LT.lt L
            (@RingPreordering.linearOrderOfIsOrdering L _ O hO).toLT
            0 (algebraMap M.carrier L a)) := by
  let L : IntermediateField M.carrier Ω :=
    IntermediateField.adjoin M.carrier ({α} : Set Ω)
  let hi : IsIntegral M.carrier α := ⟨q, hqmonic, hroot⟩
  let pb : PowerBasis M.carrier L :=
    IntermediateField.adjoin.powerBasis hi
  have hdim : pb.dim = q.natDegree := by
    dsimp [pb, IntermediateField.adjoin.powerBasis]
    rw [minpoly_eq_of_monic_irreducible_root hqmonic hqirr hroot]
  have hodd : Odd pb.dim := by
    rw [hdim]
    exact hqodd
  obtain ⟨O, hO, hnonneg, hpos⟩ :=
    exists_orderedAlgebraExtension_of_odd_powerBasis (F := M.carrier) (K := L) pb hodd
  exact ⟨L, pb, O, hO, rfl, hdim, hodd, rfl, hnonneg, hpos⟩

/-!
### Maximality consumes the odd ordering witness
-/

/-- An odd-degree polynomial over a maximal ordered intermediate field has a root there. -/
theorem exists_root_of_odd_natDegree_of_isMax
    (M : Intermediate F) (hmax : IsMax M) {p : M.carrier[X]}
    (hodd : Odd p.natDegree) :
    ∃ a : M.carrier, p.IsRoot a := by
  obtain ⟨q, hqodd, hqmonic, hqirr, hqdiv⟩ :=
    Polynomial.exists_odd_natDegree_monic_irreducible_factor hodd
  have hqdeg : q.degree ≠ 0 := by
    intro hdeg
    have hqnat : q.natDegree ≠ 0 := by
      rcases hqodd with ⟨n, hn⟩
      intro hzero
      rw [hzero] at hn
      omega
    exact hqnat (natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq hdeg))
  obtain ⟨α, hα⟩ := exists_root_over_intermediate (F := F) M hqdeg
  have hroot : Polynomial.aeval α q = 0 := by
    simpa [Polynomial.aeval_def] using hα
  obtain ⟨L, pb, O, hO, hL, hdim, hpbodd, hgen, hnonneg, hpos⟩ :=
    exists_ordered_odd_adjoin (F := F) M hqodd hqmonic hqirr hroot
  let _ : O.IsOrdering := hO
  let _ : LinearOrder L := RingPreordering.linearOrderOfIsOrdering O
  let _ : IsStrictOrderedRing L := RingPreordering.isStrictOrderedRingOfIsOrdering O
  have hmono : Monotone (algebraMap M.carrier L) := by
    intro x y hxy
    apply sub_nonneg.mp
    have hxy' := hnonneg (y - x) (sub_nonneg.mpr hxy)
    simpa [map_sub] using hxy'
  let _ : IsOrderedModule M.carrier L := IsOrderedModule.of_algebraMap_mono hmono
  have hMLE : M ≤ M.ofOrderedSubfield L :=
    Intermediate.le_ofOrderedSubfield (F := F) M L
  have hαL : α ∈ L := by
    rw [hL]
    exact IntermediateField.mem_adjoin_of_mem M.carrier (Set.mem_singleton α)
  have hαE : α ∈ (M.ofOrderedSubfield L).carrier := by
    change α ∈ IntermediateField.restrictScalars F L
    exact hαL
  have hαM : α ∈ M.carrier :=
    maximal_contains_of_le (F := F) hmax hMLE hαE
  let a : M.carrier := ⟨α, hαM⟩
  refine ⟨a, ?_⟩
  have hαa : algebraMap M.carrier Ω a = α := by
    rfl
  apply (RingHom.injective (algebraMap M.carrier Ω))
  rw [← Polynomial.eval₂_hom]
  obtain ⟨r, hr⟩ := dvd_iff_exists_eq_mul_right.mp hqdiv
  rw [hr, Polynomial.eval₂_mul, hαa, hα, map_zero, zero_mul]

end OrderedRealClosure
end RatFuncWittLocalGlobal
