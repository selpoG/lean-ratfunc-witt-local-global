/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.FiniteDimensional.Compression.Real
import RatFuncWittLocalGlobal.Polynomial.OrderedImageSign

/-!
# Ordered-image transport for binary-tail compression
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u w

noncomputable section

namespace FinitePolynomialState

variable {R : Type u} {κ : Type w} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R] [Fintype κ]
  {a : Sum (Fin 2) κ → _root_.RatFunc R}

/-- Ordinary realization of a binary-tail skeleton transports to every
same-universe ordered field image. -/
theorem binaryTailSkeleton_allOrdered
    (T : FinitePolynomialState a) (S : SignedLinearRootSkeleton R)
    (hSroots : S.roots ⊆ T.realRoots)
    (hSeval : ∀ y : R, y ∉ T.realRoots →
      (binaryTailCompressionRequiredSign
        (fun i => (T.A (Sum.inl i)).eval y)
        (fun j => (T.A (Sum.inr j)).eval y)).Holds (S.poly.eval y)) :
    ∀ {L : Type u} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
      (f : _root_.RatFunc R →+* L),
      (binaryTailCompressionRequiredSign
        (fun i => f (algebraMap (Polynomial R) (_root_.RatFunc R)
          (T.A (Sum.inl i))))
        (fun j => f (algebraMap (Polynomial R) (_root_.RatFunc R)
          (T.A (Sum.inr j))))).Holds
        (f (algebraMap (Polynomial R) (_root_.RatFunc R) S.poly)) := by
  classical
  intro L _ _ _ f
  let φ : R →+* L := f.comp (algebraMap R (_root_.RatFunc R))
  let x : L := f _root_.RatFunc.X
  let roots : Finset R := T.realRoots
  have hφ : StrictMono φ := realClosed_ringHom_strictMono φ
  have heval (p : Polynomial R) :
      f (algebraMap (Polynomial R) (_root_.RatFunc R) p) = p.eval₂ φ x := by
    calc
      f (algebraMap (Polynomial R) (_root_.RatFunc R) p) =
          f (p.eval₂ _root_.RatFunc.C _root_.RatFunc.X) := by
        exact congrArg f (_root_.RatFunc.aeval_X_left_eq_algebraMap p).symm
      _ = p.eval₂ φ x := by
        simpa [φ, x] using
          (Polynomial.hom_eval₂ p _root_.RatFunc.C f _root_.RatFunc.X)
  have hx : ∀ r ∈ roots, x ≠ φ r := by
    intro r _
    exact ratFunc_X_image_ne_base f r
  rcases exists_base_sample_with_same_finite_cut φ hφ roots x hx with
    ⟨y, hy, hcut⟩
  let A : Sum (Fin 2) κ → L := fun i => (T.A i).eval₂ φ x
  let B : Sum (Fin 2) κ → R := fun i => (T.A i).eval y
  have hA (i : Sum (Fin 2) κ) : A i ≠ 0 := by
    have hpoly : algebraMap (Polynomial R) (_root_.RatFunc R) (T.A i) ≠ 0 :=
      _root_.RatFunc.algebraMap_ne_zero (T.normal_form i).1
    have hmap : f (algebraMap (Polynomial R) (_root_.RatFunc R) (T.A i)) ≠ 0 :=
      fun hz => hpoly (f.injective (by simpa using hz))
    change (T.A i).eval₂ φ x ≠ 0
    rw [← heval]
    exact hmap
  have hB (i : Sum (Fin 2) κ) : B i ≠ 0 :=
    T.eval_ne_zero_of_not_mem_realRoots hy i
  have hpos (i : Sum (Fin 2) κ) : 0 < A i ↔ 0 < B i := by
    apply polynomial_eval₂_pos_iff_eval_of_same_finite_cut
      φ hφ roots (T.A i) (T.normal_form i).1 hx
    · intro r hr
      exact (T.mem_realRoots_iff r).mpr ⟨i, hr⟩
    · exact hcut
  have hsign : binaryTailCompressionRequiredSign
      (fun i => A (Sum.inl i)) (fun j => A (Sum.inr j)) =
        binaryTailCompressionRequiredSign
          (fun i => B (Sum.inl i)) (fun j => B (Sum.inr j)) :=
    binaryTailCompressionRequiredSign_eq_of_pos_iff
      _ _ _ _ (fun j => hA (Sum.inr j)) (fun j => hB (Sum.inr j))
      (fun i => hpos (Sum.inl i)) (fun j => hpos (Sum.inr j))
  have hSmap : S.poly.eval₂ φ x ≠ 0 := by
    have hpoly : algebraMap (Polynomial R) (_root_.RatFunc R) S.poly ≠ 0 :=
      _root_.RatFunc.algebraMap_ne_zero S.poly_ne_zero
    have hmap : f (algebraMap (Polynomial R) (_root_.RatFunc R) S.poly) ≠ 0 :=
      fun hz => hpoly (f.injective (by simpa using hz))
    rw [← heval]
    exact hmap
  have hSeval0 : S.poly.eval y ≠ 0 := by
    intro hz
    exact hy (hSroots ((S.eval_poly_eq_zero_iff y).mp hz))
  have hSpos : 0 < S.poly.eval₂ φ x ↔ 0 < S.poly.eval y := by
    apply polynomial_eval₂_pos_iff_eval_of_same_finite_cut
      φ hφ roots S.poly S.poly_ne_zero hx
    · intro r hr
      exact hSroots ((S.eval_poly_eq_zero_iff r).mp hr)
    · exact hcut
  have hbase := hSeval y hy
  have hbase' : (binaryTailCompressionRequiredSign
      (fun i => A (Sum.inl i)) (fun j => A (Sum.inr j))).Holds
        (S.poly.eval y) := by
    rw [hsign]
    exact hbase
  have hmapped := (StrictSign.holds_iff_of_pos_iff
    (binaryTailCompressionRequiredSign
      (fun i => A (Sum.inl i)) (fun j => A (Sum.inr j)))
    hSmap hSeval0 hSpos).mpr hbase'
  simp only [A] at hmapped
  rw [heval]
  simpa only [heval] using hmapped

/-- Every finite binary-tail polynomial state admits one compression
coefficient with the required sign in all same-universe ordered images. -/
theorem exists_binaryTailSkeleton_allOrdered
    (T : FinitePolynomialState a) :
    ∃ S : SignedLinearRootSkeleton R,
      ∀ {L : Type u} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
        (f : _root_.RatFunc R →+* L),
        (binaryTailCompressionRequiredSign
          (fun i => f (algebraMap (Polynomial R) (_root_.RatFunc R)
            (T.A (Sum.inl i))))
          (fun j => f (algebraMap (Polynomial R) (_root_.RatFunc R)
            (T.A (Sum.inr j))))).Holds
          (f (algebraMap (Polynomial R) (_root_.RatFunc R) S.poly)) := by
  rcases T.exists_binaryTailSkeleton_eval with ⟨S, hSroots, hSeval⟩
  exact ⟨S, T.binaryTailSkeleton_allOrdered S hSroots hSeval⟩

end FinitePolynomialState

end

end RatFuncWittLocalGlobal
