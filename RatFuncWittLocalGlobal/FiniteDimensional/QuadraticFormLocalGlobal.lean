/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.FiniteDimensional.DiagonalLocalGlobal
import RatFuncWittLocalGlobal.FiniteDimensional.QuadraticForm
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

/-!
# Local-global principle for finite-dimensional quadratic forms

An orthogonal basis identifies an arbitrary finite-dimensional quadratic form
with a weighted diagonal form.  The same basis after tensor-product base
change gives the corresponding identification over every extension field.
This transports the completed total diagonal theorem to Mathlib's general
`QuadraticForm` interface.
-/

open scoped TensorProduct

namespace RatFuncWittLocalGlobal

universe u v w

noncomputable section

/-- An isometric equivalence preserves failure of anisotropy. -/
theorem quadraticMap_isometryEquiv_not_anisotropic_iff
    {F : Type u} [CommSemiring F]
    {M₁ : Type v} {M₂ : Type w}
    [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module F M₁] [Module F M₂]
    {Q₁ : QuadraticForm F M₁} {Q₂ : QuadraticForm F M₂}
    (e : Q₁.IsometryEquiv Q₂) :
    ¬ Q₁.Anisotropic ↔ ¬ Q₂.Anisotropic := by
  simp only [QuadraticMap.not_anisotropic_iff_exists]
  constructor
  · rintro ⟨x, hx, hQx⟩
    refine ⟨e x, ?_, ?_⟩
    · exact fun h => hx (e.injective (by simpa using h))
    · rw [e.map_app, hQx]
  · rintro ⟨y, hy, hQy⟩
    refine ⟨e.symm y, ?_, ?_⟩
    · exact fun h => hy (e.symm.injective (by simpa using h))
    · rw [e.symm.map_app, hQy]

/-- An orthogonal basis remains an orthogonal diagonalization after field
extension, with each weight sent through the algebra map. -/
noncomputable def quadraticFormBaseChangeIsometryWeightedSumSquares
    {F : Type u} {K : Type v} {V : Type w}
    [Field F] [CharZero F] [Field K] [CharZero K] [Algebra F K]
    [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι F V)
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) :
    (Q.baseChange K).IsometryEquiv
      (QuadraticMap.weightedSumSquares K
        (fun i => algebraMap F K (Q (b i)))) := by
  let bK := b.baseChange K
  have hbK : (QuadraticMap.associated (Q.baseChange K)).IsOrthoᵢ bK := by
    intro i j hij
    change ((QuadraticMap.associated (Q.baseChange K)) (bK i)) (bK j) = 0
    rw [QuadraticForm.associated_baseChange, Module.Basis.baseChange_apply,
      Module.Basis.baseChange_apply, LinearMap.BilinForm.baseChange_tmul]
    rw [hb hij]
    simp
  let e := (Q.baseChange K).isometryEquivBasisRepr bK
  rw [QuadraticMap.basisRepr_eq_of_iIsOrtho _ _ hbK] at e
  have hw : (fun i => (Q.baseChange K) (bK i)) =
      fun i => algebraMap F K (Q (b i)) := by
    funext i
    simp [bK, QuadraticForm.baseChange_tmul, Algebra.smul_def]
  exact e.trans (QuadraticForm.weightedSumSquaresCongr hw)

/-- Same-universe local-global principle for an arbitrary finite-dimensional
quadratic form of dimension at least three over `RatFunc R`.  Isotropy is
expressed as failure of Mathlib's `QuadraticMap.Anisotropic` predicate. -/
theorem quadraticForm_not_anisotropic_iff_forall_realClosedExtension_same_universe
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R]
    {V : Type w} [AddCommGroup V] [Module (_root_.RatFunc R) V]
    [FiniteDimensional (_root_.RatFunc R) V]
    (hcard : 3 ≤ Module.finrank (_root_.RatFunc R) V)
    (Q : QuadraticForm (_root_.RatFunc R) V) :
    ¬ Q.Anisotropic ↔
      ∀ {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
        [IsRealClosed K] [Algebra (_root_.RatFunc R) K],
        ¬ (Q.baseChange K).Anisotropic := by
  classical
  let F := _root_.RatFunc R
  obtain ⟨b, hb⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis
      (QuadraticForm.associated_isSymm F Q)
  let a : Fin (Module.finrank F V) → F := fun i => Q (b i)
  let e := Q.isometryEquivWeightedSumSquares b hb
  have hbase : ¬ Q.Anisotropic ↔ Diagonal.Isotropic a := by
    calc
      ¬ Q.Anisotropic ↔
          ¬ (QuadraticMap.weightedSumSquares F a).Anisotropic :=
        quadraticMap_isometryEquiv_not_anisotropic_iff e
      _ ↔ Diagonal.Isotropic a := by
        simpa [Diagonal.diagonalQuadraticForm] using
          (Diagonal.isotropic_iff_not_diagonalQuadraticForm_anisotropic a).symm
  constructor
  · intro hQ K _ _ _ _ _
    have ha : Diagonal.Isotropic a := hbase.mp hQ
    have haK : Diagonal.Isotropic (fun i => algebraMap F K (a i)) :=
      Diagonal.isotropic_baseChange ha
    let eK := quadraticFormBaseChangeIsometryWeightedSumSquares
      (K := K) Q b hb
    apply (quadraticMap_isometryEquiv_not_anisotropic_iff eK).mpr
    exact (Diagonal.isotropic_iff_not_diagonalQuadraticForm_anisotropic
      (fun i => algebraMap F K (a i))).mp haK
  · intro hlocal
    apply hbase.mpr
    apply
      (diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_same_universe_total
        (by simpa [F] using hcard) a).mpr
    intro K _ _ _ _ _
    let eK := quadraticFormBaseChangeIsometryWeightedSumSquares
      (K := K) Q b hb
    apply (Diagonal.isotropic_iff_not_diagonalQuadraticForm_anisotropic
      (fun i => algebraMap F K (a i))).mpr
    exact (quadraticMap_isometryEquiv_not_anisotropic_iff eK).mp hlocal

/-- Universe-parameterized quadratic-form local-global theorem under the
precise ordered-real-closure input for `RatFunc R`. -/
theorem quadraticForm_not_anisotropic_iff_forall_realClosedExtension_of_ratFuncClosure
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R]
    {V : Type w} [AddCommGroup V] [Module (_root_.RatFunc R) V]
    [FiniteDimensional (_root_.RatFunc R) V]
    (hclosure : RatFunc.RatFuncOrderedRealClosedExtension.{u, v} R)
    (hcard : 3 ≤ Module.finrank (_root_.RatFunc R) V)
    (Q : QuadraticForm (_root_.RatFunc R) V) :
    ¬ Q.Anisotropic ↔
      ∀ {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
        [IsRealClosed K] [Algebra (_root_.RatFunc R) K],
        ¬ (Q.baseChange K).Anisotropic := by
  classical
  let F := _root_.RatFunc R
  obtain ⟨b, hb⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis
      (QuadraticForm.associated_isSymm F Q)
  let a : Fin (Module.finrank F V) → F := fun i => Q (b i)
  let e := Q.isometryEquivWeightedSumSquares b hb
  have hbase : ¬ Q.Anisotropic ↔ Diagonal.Isotropic a := by
    calc
      ¬ Q.Anisotropic ↔
          ¬ (QuadraticMap.weightedSumSquares F a).Anisotropic :=
        quadraticMap_isometryEquiv_not_anisotropic_iff e
      _ ↔ Diagonal.Isotropic a := by
        simpa [Diagonal.diagonalQuadraticForm] using
          (Diagonal.isotropic_iff_not_diagonalQuadraticForm_anisotropic a).symm
  constructor
  · intro hQ K _ _ _ _ _
    have ha : Diagonal.Isotropic a := hbase.mp hQ
    have haK : Diagonal.Isotropic (fun i => algebraMap F K (a i)) :=
      Diagonal.isotropic_baseChange ha
    let eK := quadraticFormBaseChangeIsometryWeightedSumSquares
      (K := K) Q b hb
    apply (quadraticMap_isometryEquiv_not_anisotropic_iff eK).mpr
    exact (Diagonal.isotropic_iff_not_diagonalQuadraticForm_anisotropic
      (fun i => algebraMap F K (a i))).mp haK
  · intro hlocal
    apply hbase.mpr
    apply
      (diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_of_ratFuncClosure
        hclosure (by simpa [F] using hcard) a).mpr
    intro K _ _ _ _ _
    let eK := quadraticFormBaseChangeIsometryWeightedSumSquares
      (K := K) Q b hb
    apply (Diagonal.isotropic_iff_not_diagonalQuadraticForm_anisotropic
      (fun i => algebraMap F K (a i))).mpr
    exact (quadraticMap_isometryEquiv_not_anisotropic_iff eK).mp hlocal

/-- Universe-parameterized quadratic-form local-global theorem under a
real-closure input for every ordered field in the base universe. -/
theorem quadraticForm_not_anisotropic_iff_forall_realClosedExtension_of_orderedFieldClosure
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R]
    {V : Type w} [AddCommGroup V] [Module (_root_.RatFunc R) V]
    [FiniteDimensional (_root_.RatFunc R) V]
    (hclosure : RatFunc.OrderedFieldRealClosedExtension.{u, v})
    (hcard : 3 ≤ Module.finrank (_root_.RatFunc R) V)
    (Q : QuadraticForm (_root_.RatFunc R) V) :
    ¬ Q.Anisotropic ↔
      ∀ {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
        [IsRealClosed K] [Algebra (_root_.RatFunc R) K],
        ¬ (Q.baseChange K).Anisotropic :=
  quadraticForm_not_anisotropic_iff_forall_realClosedExtension_of_ratFuncClosure
    (RatFunc.ratFuncOrderedRealClosedExtension_of_orderedFieldRealClosedExtension
      hclosure) hcard Q

end

end RatFuncWittLocalGlobal
