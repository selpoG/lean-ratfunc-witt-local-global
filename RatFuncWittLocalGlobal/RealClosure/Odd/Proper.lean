/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.RealClosure.Odd.Induction
import RatFuncWittLocalGlobal.RealClosure.Odd.SpanBridge

/-!
# Properness of the odd power-basis square span

For an odd-dimensional power basis, the additive span of nonnegative base
scalars and squares is proper.  A hypothetical representation of `-1` lifts
to a bounded square polynomial; the odd minimal polynomial of the generator
then divides that polynomial plus one, contradicting the bounded-cone
divisibility lemma.
-/

namespace RatFuncWittLocalGlobal

open scoped _root_.Polynomial
open _root_.Polynomial

universe u v

namespace OrderedRealClosure

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {K : Type v} [Field K] [Algebra F K]

/-- The base-square span is proper for an odd-dimensional power basis. -/
theorem minus_one_notMem_baseSquareSpan_of_odd_powerBasis
    (pb : PowerBasis F K) (hodd : Odd pb.dim) :
    (-1 : K) ∉ baseSquareSpan (F := F) (K := K) := by
  intro hminus
  obtain ⟨g, hgeval, hg⟩ := mem_baseSquareSpan_aeval (F := F) (K := K) pb hminus
  have hroot : Polynomial.aeval pb.gen (g + 1) = 0 := by
    rw [Polynomial.aeval_add, hgeval, Polynomial.aeval_one]
    simp
  have hdiv : minpoly F pb.gen ∣ g + 1 := minpoly.dvd F pb.gen hroot
  have hfM : (minpoly F pb.gen).Monic := minpoly.monic pb.isIntegral_gen
  have hfI : Irreducible (minpoly F pb.gen) :=
    minpoly.irreducible pb.isIntegral_gen
  have hfO : Odd (minpoly F pb.gen).natDegree := by
    rw [pb.natDegree_minpoly]
    exact hodd
  have hg' : g ∈ boundedSquarePolynomialCone (minpoly F pb.gen).natDegree := by
    rw [pb.natDegree_minpoly]
    exact hg
  have hnot : ¬ (minpoly F pb.gen) ∣ g + 1 :=
    not_dvd_add_one_of_mem_boundedSquarePolynomialCone
      (F := F) (f := minpoly F pb.gen) (g := g) hfM hfI hfO hg'
  exact hnot hdiv

/-! The proper span feeds directly into the maximal-order extension witness. -/

theorem exists_orderedAlgebraExtension_of_odd_powerBasis
    (pb : PowerBasis F K) (hodd : Odd pb.dim) :
    ∃ (O : _root_.RingPreordering K) (hO : O.IsOrdering),
      (∀ a : F, 0 ≤ a →
        @LE.le K
          (@RatFuncWittLocalGlobal.RingPreordering.linearOrderOfIsOrdering K _ O hO).toLE
          0 (algebraMap F K a)) ∧
      (∀ a : F, 0 < a →
        @LT.lt K
          (@RatFuncWittLocalGlobal.RingPreordering.linearOrderOfIsOrdering K _ O hO).toLT
          0 (algebraMap F K a)) := by
  apply exists_orderedAlgebraExtension_of_baseSquareSpanProper
  exact minus_one_notMem_baseSquareSpan_of_odd_powerBasis pb hodd

end OrderedRealClosure
end RatFuncWittLocalGlobal
