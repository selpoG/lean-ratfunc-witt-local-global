/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.FiniteDimensional.Compression.Transport
import RatFuncWittLocalGlobal.FiniteDimensional.Compression.Reconstruction
import RatFuncWittLocalGlobal.Ternary.LocalGlobal

/-!
# Dimension step from binary-tail compression

If the ordering obstruction is sufficient for the tail enlarged by one
coordinate, then it is sufficient for the form obtained by adjoining a binary
head to the original tail.  Thus the construction advances dimension by one.
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u w z

noncomputable section

/-- Ordering-obstruction sufficiency for regular diagonal forms on a fixed
finite index type. -/
def DiagonalOrderingObstructionSufficiency
    (R : Type u) [Field R] (ι : Type w) [Fintype ι] : Prop :=
  ∀ (a : ι → _root_.RatFunc R), (∀ i, a i ≠ 0) →
    ¬ RatFunc.FiniteSameStrictSignOrdering a → Diagonal.Isotropic a

/-- Ordering-obstruction sufficiency is invariant under reindexing. -/
theorem diagonalOrderingObstructionSufficiency_reindex
    {R : Type u} {ι : Type w} {κ : Type z} [Field R] [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (h : DiagonalOrderingObstructionSufficiency R κ) :
    DiagonalOrderingObstructionSufficiency R ι := by
  intro a ha hno
  let b : κ → _root_.RatFunc R := fun j => a (e.symm j)
  have hb : ∀ j, b j ≠ 0 := fun j => ha (e.symm j)
  have hbno : ¬ RatFunc.FiniteSameStrictSignOrdering b := by
    intro hborder
    apply hno
    simpa [b] using
      ((RatFunc.finiteSameStrictSignOrdering_comp_equiv e b).mpr hborder)
  have hbiso : Diagonal.Isotropic b := h b hb hbno
  simpa [b] using (Diagonal.isotropic_comp_equiv e b).mpr hbiso

/-- Binary-tail compression turns sufficiency in dimension `card κ + 1`
into sufficiency in dimension `card κ + 2`. -/
theorem diagonalOrderingObstructionSufficiency_sum_fin_two
    {R : Type u} {κ : Type w} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] [Fintype κ] [Nonempty κ]
    (htail : DiagonalOrderingObstructionSufficiency R (Sum κ (Fin 1))) :
    DiagonalOrderingObstructionSufficiency R (Sum (Fin 2) κ) := by
  intro a ha hno
  let T := Classical.choice (finitePolynomialState_exists ha hno)
  rcases T.exists_binaryTailSkeleton_allOrdered with ⟨S, hS⟩
  let A : Sum (Fin 2) κ → _root_.RatFunc R := fun i =>
    algebraMap (Polynomial R) (_root_.RatFunc R) (T.A i)
  let c : _root_.RatFunc R :=
    algebraMap (Polynomial R) (_root_.RatFunc R) S.poly
  have hA (i : Sum (Fin 2) κ) : A i ≠ 0 :=
    _root_.RatFunc.algebraMap_ne_zero (T.normal_form i).1
  have hc : c ≠ 0 := _root_.RatFunc.algebraMap_ne_zero S.poly_ne_zero
  have hlocal : ∀ {K : Type u} [Field K] [LinearOrder K]
      [IsStrictOrderedRing K] [IsRealClosed K]
      (f : _root_.RatFunc R →+* K),
      Diagonal.TernaryIsotropic (f (A (Sum.inl 0)))
        (f (A (Sum.inl 1))) (f c) ∧
      Diagonal.Isotropic (Sum.elim
        (fun j => f (A (Sum.inr j))) (fun _ : Fin 1 => -f c)) := by
    intro K _ _ _ _ f
    have hnoA : ¬ ScalarFamilySameStrictSign (fun i => f (A i)) := by
      simpa [A] using T.not_scalarFamilySameStrictSign_map f
    have hrequired : (binaryTailCompressionRequiredSign
        (fun i => f (A (Sum.inl i)))
        (fun j => f (A (Sum.inr j)))).Holds (f c) := by
      simpa [A, c] using hS f
    have hblocks := binaryTailCompressionRequiredSign_spec
      (fun i => f (A (Sum.inl i))) (fun j => f (A (Sum.inr j)))
      (by
        intro hsame
        apply hnoA
        convert hsame using 1
        funext i
        cases i <;> rfl) hrequired
    have hheadDiag : Diagonal.Isotropic
        (![f (A (Sum.inl 0)), f (A (Sum.inl 1)), f c] : Fin 3 → K) :=
      Diagonal.isotropic_of_not_scalarFamilySameStrictSign _
        (by intro i; fin_cases i <;> simp [hA, hc]) hblocks.1
    have htailDiag : Diagonal.Isotropic (Sum.elim
        (fun j => f (A (Sum.inr j))) (fun _ : Fin 1 => -f c)) :=
      Diagonal.isotropic_of_not_scalarFamilySameStrictSign _
        (by
          intro i
          cases i with
          | inl j =>
              intro hz
              exact hA (Sum.inr j) (f.injective (by simpa using hz))
          | inr j =>
              intro hz
              exact hc (f.injective (by simpa using hz)))
        hblocks.2
    exact ⟨(Diagonal.isotropic_fin_three_iff _).mp hheadDiag, htailDiag⟩
  have htern : Diagonal.TernaryIsotropic (A (Sum.inl 0))
      (A (Sum.inl 1)) c := by
    apply (RatFunc.ternary_isotropic_iff_forall_realClosedExtension_same_universe
      _ _ _ ⟨hA (Sum.inl 0), hA (Sum.inl 1), hc⟩).mpr
    intro K _ _ _ _ _
    exact (hlocal (algebraMap (_root_.RatFunc R) K)).1
  let b : Sum κ (Fin 1) → _root_.RatFunc R :=
    Sum.elim (fun j => A (Sum.inr j)) (fun _ : Fin 1 => -c)
  have hb : ∀ i, b i ≠ 0 := by
    intro i
    cases i with
    | inl j => exact hA (Sum.inr j)
    | inr j => simpa [b] using hc
  have hbloc : ∀ {K : Type u} [Field K] [LinearOrder K]
      [IsStrictOrderedRing K] [IsRealClosed K]
      [Algebra (_root_.RatFunc R) K],
      Diagonal.Isotropic (fun i => algebraMap (_root_.RatFunc R) K (b i)) := by
    intro K _ _ _ _ _
    have h := (hlocal (algebraMap (_root_.RatFunc R) K)).2
    convert h using 1
    funext i
    cases i with
    | inl j => rfl
    | inr j => simp [b]
  have hbno : ¬ RatFunc.FiniteSameStrictSignOrdering b :=
    (RatFunc.forall_realClosedExtension_iff_not_finiteSameStrictSignOrdering
      OrderedRealClosure.orderedFieldRealClosedExtension_same_universe
      b hb).mp hbloc
  have hbtail : Diagonal.Isotropic b := htail b hb hbno
  have hsum : Diagonal.Isotropic
      (Diagonal.sumTypeCoeff (A (Sum.inl 0)) (A (Sum.inl 1))
        (fun j => A (Sum.inr j))) :=
    Diagonal.isotropic_sumType_of_ternary_of_tailAdjoinNeg
      (A (Sum.inl 0)) (A (Sum.inl 1)) c hc
      (fun j => A (Sum.inr j)) htern (by simpa [b] using hbtail)
  apply T.isotropy_iff.mpr
  change Diagonal.Isotropic A
  have heq : Diagonal.sumTypeCoeff (A (Sum.inl 0)) (A (Sum.inl 1))
      (fun j => A (Sum.inr j)) = A := by
    funext i
    cases i with
    | inl i => fin_cases i <;> rfl
    | inr j => rfl
  rw [heq] at hsum
  exact hsum

/-- Finite-dimensional successor form of the binary-tail step. -/
theorem diagonalOrderingObstructionSufficiency_fin_add_two
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] (n : ℕ) (hn : 0 < n)
    (h : DiagonalOrderingObstructionSufficiency R (Fin (n + 1))) :
    DiagonalOrderingObstructionSufficiency R (Fin (2 + n)) := by
  let _ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let htail : DiagonalOrderingObstructionSufficiency R
      (Sum (Fin n) (Fin 1)) :=
    diagonalOrderingObstructionSufficiency_reindex
      (finSumFinEquiv (m := n) (n := 1)) h
  have hsum : DiagonalOrderingObstructionSufficiency R
      (Sum (Fin 2) (Fin n)) :=
    diagonalOrderingObstructionSufficiency_sum_fin_two htail
  exact diagonalOrderingObstructionSufficiency_reindex
    (finSumFinEquiv (m := 2) (n := n)).symm hsum

/-- Ternary local-global gives the base case for dimension induction. -/
theorem diagonalOrderingObstructionSufficiency_fin_three
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] :
    DiagonalOrderingObstructionSufficiency R (Fin 3) := by
  intro a ha hno
  have hlocal : ∀ {K : Type u}
      [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
      [Algebra (_root_.RatFunc R) K],
      Diagonal.Isotropic (fun i => algebraMap (_root_.RatFunc R) K (a i)) :=
    RatFunc.forall_realClosedExtension_of_not_finiteSameStrictSignOrdering
      a ha hno
  have htern : Diagonal.TernaryIsotropic (a 0) (a 1) (a 2) := by
    apply (RatFunc.ternary_isotropic_iff_forall_realClosedExtension_same_universe
      (a 0) (a 1) (a 2) ⟨ha 0, ha 1, ha 2⟩).mpr
    intro K _ _ _ _ _
    exact (Diagonal.isotropic_fin_three_iff _).mp (hlocal (K := K))
  exact (Diagonal.isotropic_fin_three_iff a).mpr htern

/-- Ordering-obstruction sufficiency in every finite dimension at least
three, presented as `Fin (n + 3)`. -/
theorem diagonalOrderingObstructionSufficiency_fin_add_three
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] (n : ℕ) :
    DiagonalOrderingObstructionSufficiency R (Fin (n + 3)) := by
  induction n with
  | zero => simpa using (diagonalOrderingObstructionSufficiency_fin_three (R := R))
  | succ n ih =>
      have hstep := diagonalOrderingObstructionSufficiency_fin_add_two
        (R := R) (n + 2) (by omega) (by simpa [Nat.add_assoc] using ih)
      have heq : 2 + (n + 2) = Nat.succ n + 3 := by omega
      exact diagonalOrderingObstructionSufficiency_reindex
        (Equiv.cast (congrArg Fin heq.symm)) hstep

/-- The ordering obstruction is sufficient for every regular finite diagonal
form of dimension at least three. -/
theorem diagonal_isotropic_of_not_finiteSameStrictSignOrdering_of_card_ge_three
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] {ι : Type w} [Fintype ι]
    (hcard : 3 ≤ Fintype.card ι)
    (a : ι → _root_.RatFunc R) (ha : ∀ i, a i ≠ 0)
    (hno : ¬ RatFunc.FiniteSameStrictSignOrdering a) :
    Diagonal.Isotropic a := by
  let n := Fintype.card ι - 3
  have hn : n + 3 = Fintype.card ι := Nat.sub_add_cancel hcard
  have hfin : DiagonalOrderingObstructionSufficiency R
      (Fin (Fintype.card ι)) :=
    diagonalOrderingObstructionSufficiency_reindex
      (Equiv.cast (congrArg Fin hn.symm))
      (diagonalOrderingObstructionSufficiency_fin_add_three (R := R) n)
  have hι : DiagonalOrderingObstructionSufficiency R ι :=
    diagonalOrderingObstructionSufficiency_reindex (Fintype.equivFin ι) hfin
  exact hι a ha hno

end
end RatFuncWittLocalGlobal
