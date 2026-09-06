/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Root facts for squarefree polynomials
-/

namespace RatFuncWittLocalGlobal

universe u

theorem rootMultiplicity_eq_one_of_squarefree_of_isRoot
    {R : Type u} [Field R] {f : Polynomial R} {a : R}
    (hf : Squarefree f) (hroot : f.IsRoot a) :
    f.rootMultiplicity a = 1 := by
  have hf0 : f ≠ 0 := hf.ne_zero
  have hnot_sq : ¬ (Polynomial.X - Polynomial.C a) ^ 2 ∣ f := by
    intro hsq
    exact Polynomial.not_isUnit_X_sub_C a
      (hf (Polynomial.X - Polynomial.C a) (by simpa [pow_two] using hsq))
  have hle : f.rootMultiplicity a ≤ 1 := by
    exact (Polynomial.rootMultiplicity_le_iff hf0 a 1).mpr
      (by simpa [pow_succ, pow_two] using hnot_sq)
  have hpos : 0 < f.rootMultiplicity a := (Polynomial.rootMultiplicity_pos hf0).mpr hroot
  omega

theorem eval_divByMonic_X_sub_C_ne_zero_of_squarefree_of_isRoot
    {R : Type u} [Field R] {f : Polynomial R} {a : R}
    (hf : Squarefree f) (hroot : f.IsRoot a) :
    (f /ₘ (Polynomial.X - Polynomial.C a)).eval a ≠ 0 := by
  have hmult : f.rootMultiplicity a = 1 :=
    rootMultiplicity_eq_one_of_squarefree_of_isRoot hf hroot
  have hf0 : f ≠ 0 := hf.ne_zero
  simpa [hmult] using Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero (p := f) a hf0

theorem exists_associated_X_sub_C_of_irreducible_of_natDegree_eq_one
    {R : Type u} [Field R] {π : Polynomial R}
    (hπ : Irreducible π) (hdeg : π.natDegree = 1) :
    ∃ a : R, Associated π (Polynomial.X - Polynomial.C a) := by
  have hdegree : π.degree = 1 := by
    have hπ0 : π ≠ 0 := hπ.ne_zero
    simpa [hdeg] using Polynomial.degree_eq_natDegree hπ0
  rcases Polynomial.exists_root_of_degree_eq_one hdegree with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hdiv : Polynomial.X - Polynomial.C a ∣ π := Polynomial.dvd_iff_isRoot.mpr ha
  have hle : π.natDegree ≤ (Polynomial.X - Polynomial.C a : Polynomial R).natDegree := by
    rw [hdeg, Polynomial.natDegree_X_sub_C]
  exact (Polynomial.associated_of_dvd_of_natDegree_le hdiv hπ.ne_zero hle).symm

theorem exists_eq_X_sub_C_of_irreducible_monic_of_natDegree_eq_one
    {R : Type u} [Field R] {π : Polynomial R}
    (hπ : Irreducible π) (hπmonic : π.Monic) (hdeg : π.natDegree = 1) :
    ∃ a : R, π = Polynomial.X - Polynomial.C a := by
  rcases exists_associated_X_sub_C_of_irreducible_of_natDegree_eq_one hπ hdeg with ⟨a, ha⟩
  exact ⟨a, Polynomial.eq_of_monic_of_associated hπmonic
    (Polynomial.monic_X_sub_C a) ha⟩

theorem monic_of_mem_normalizedFactors
    {R : Type u} [Field R] [DecidableEq R] {P π : Polynomial R}
    (hπ : π ∈ UniqueFactorizationMonoid.normalizedFactors P) :
    π.Monic := by
  have hπ0 : π ≠ 0 := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hπ
  have hnorm : normalize π = π :=
    UniqueFactorizationMonoid.normalize_normalized_factor π hπ
  exact (Polynomial.normalize_eq_self_iff_monic hπ0).mp hnorm

theorem not_isRoot_of_irreducible_of_natDegree_ne_one
    {R : Type u} [Field R] {π : Polynomial R}
    (hπ : Irreducible π) (hdeg : π.natDegree ≠ 1) (a : R) :
    ¬ π.IsRoot a := by
  intro hroot
  exact hdeg (Polynomial.natDegree_eq_of_degree_eq_some
    (Polynomial.degree_eq_one_of_irreducible_of_root hπ hroot))

theorem eval_ne_zero_of_irreducible_of_natDegree_ne_one
    {R : Type u} [Field R] {π : Polynomial R}
    (hπ : Irreducible π) (hdeg : π.natDegree ≠ 1) (a : R) :
    π.eval a ≠ 0 := by
  exact not_isRoot_of_irreducible_of_natDegree_ne_one hπ hdeg a

end RatFuncWittLocalGlobal
