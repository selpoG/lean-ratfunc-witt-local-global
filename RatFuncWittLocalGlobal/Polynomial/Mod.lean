/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Polynomial congruences modulo a square

This file introduces the elementary congruence predicate needed for the
polynomial Legendre route.
-/

namespace RatFuncWittLocalGlobal

variable {R : Type*} [CommRing R]

/-- `a` is a square modulo the polynomial `m`. -/
def IsSquareMod (m a : _root_.Polynomial R) : Prop :=
  ∃ x : _root_.Polynomial R, m ∣ x ^ 2 - a

theorem isSquareMod_one (a : _root_.Polynomial R) :
    IsSquareMod 1 a :=
  ⟨0, one_dvd _⟩

theorem isSquare_quotient_span_singleton_of_isSquareMod
    {m a : _root_.Polynomial R} (h : IsSquareMod m a) :
    IsSquare (Ideal.Quotient.mk (Ideal.span ({m} : Set (_root_.Polynomial R))) a) := by
  rcases h with ⟨x, hx⟩
  refine ⟨Ideal.Quotient.mk (Ideal.span ({m} : Set (_root_.Polynomial R))) x, ?_⟩
  have hmem :
      x ^ 2 - a ∈ Ideal.span ({m} : Set (_root_.Polynomial R)) := by
    simpa [Ideal.mem_span_singleton] using hx
  have hq :
      Ideal.Quotient.mk (Ideal.span ({m} : Set (_root_.Polynomial R))) (x ^ 2) =
        Ideal.Quotient.mk (Ideal.span ({m} : Set (_root_.Polynomial R))) a :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      (I := Ideal.span ({m} : Set (_root_.Polynomial R))) (x ^ 2) a).mpr hmem
  simpa [pow_two] using hq.symm

theorem isSquareMod_of_isSquare_quotient_span_singleton
    {m a : _root_.Polynomial R}
    (h : IsSquare (Ideal.Quotient.mk (Ideal.span ({m} : Set (_root_.Polynomial R))) a)) :
    IsSquareMod m a := by
  rcases h with ⟨xbar, hxbar⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
  refine ⟨x, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_dvd]
  have hq :
      Ideal.Quotient.mk (Ideal.span ({m} : Set (_root_.Polynomial R))) (x ^ 2) =
        Ideal.Quotient.mk (Ideal.span ({m} : Set (_root_.Polynomial R))) a := by
    simpa [pow_two] using hxbar.symm
  have hzero :
      Ideal.Quotient.mk (Ideal.span ({m} : Set (_root_.Polynomial R))) (x ^ 2 - a) = 0 := by
    simpa [map_sub] using sub_eq_zero.mpr hq
  exact hzero

theorem IsSquareMod.of_dvd
    {m n a : _root_.Polynomial R} (hmn : m ∣ n) (h : IsSquareMod n a) :
    IsSquareMod m a := by
  rcases h with ⟨x, hx⟩
  exact ⟨x, hmn.trans hx⟩

theorem IsSquareMod.of_associated
    {m n a : _root_.Polynomial R} (hmn : Associated m n) (h : IsSquareMod n a) :
    IsSquareMod m a :=
  h.of_dvd hmn.dvd

theorem isSquareMod_associated_iff
    {m n a : _root_.Polynomial R} (hmn : Associated m n) :
    IsSquareMod m a ↔ IsSquareMod n a := by
  constructor
  · intro h
    exact h.of_dvd hmn.dvd'
  · intro h
    exact h.of_dvd hmn.dvd

theorem IsSquareMod.of_dvd_sub
    {m a b : _root_.Polynomial R} (hab : m ∣ a - b) (h : IsSquareMod m a) :
    IsSquareMod m b := by
  rcases h with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hsum : m ∣ (x ^ 2 - a) + (a - b) := dvd_add hx hab
  convert hsum using 1
  ring

theorem IsSquareMod.mul_square
    {m a : _root_.Polynomial R} (h : IsSquareMod m a) (b : _root_.Polynomial R) :
    IsSquareMod m (a * b ^ 2) := by
  rcases h with ⟨x, hx⟩
  refine ⟨x * b, ?_⟩
  have hmul : m ∣ (x ^ 2 - a) * b ^ 2 := dvd_mul_of_dvd_left hx _
  convert hmul using 1
  ring

theorem IsSquareMod.of_mul_square_of_isCoprime
    {m a q : _root_.Polynomial R} (hqm : IsCoprime q m)
    (h : IsSquareMod m (a * q ^ 2)) :
    IsSquareMod m a := by
  rcases h with ⟨x, hx⟩
  rcases hqm with ⟨s, t, hst⟩
  refine ⟨x * s, ?_⟩
  have hfirst : m ∣ (x ^ 2 - a * q ^ 2) * s ^ 2 :=
    dvd_mul_of_dvd_left hx _
  have hqs : m ∣ q * s - 1 := by
    have hident : q * s - 1 = -(t * m) := by
      rw [← hst]
      ring
    rw [hident]
    exact dvd_neg.mpr (dvd_mul_left m t)
  have hsq : m ∣ (q * s) ^ 2 - 1 := by
    rw [show (q * s) ^ 2 - 1 = (q * s - 1) * (q * s + 1) by ring]
    exact dvd_mul_of_dvd_left hqs _
  have hsecond : m ∣ a * ((q * s) ^ 2 - 1) :=
    dvd_mul_of_dvd_right hsq a
  have hsum : m ∣
      (x ^ 2 - a * q ^ 2) * s ^ 2 + a * ((q * s) ^ 2 - 1) :=
    dvd_add hfirst hsecond
  convert hsum using 1
  ring

theorem polynomial_dvd_sq_sub_sq_of_dvd_sub
    {m x y : _root_.Polynomial R} (hxy : m ∣ y - x) :
    m ∣ y ^ 2 - x ^ 2 := by
  rw [show y ^ 2 - x ^ 2 = (y - x) * (y + x) by ring]
  exact dvd_mul_of_dvd_left hxy _

theorem polynomial_dvd_sq_sub_of_dvd_sub_of_dvd_sq_sub
    {m a x y : _root_.Polynomial R} (hxy : m ∣ y - x) (hx : m ∣ x ^ 2 - a) :
    m ∣ y ^ 2 - a := by
  have hsq : m ∣ y ^ 2 - x ^ 2 := polynomial_dvd_sq_sub_sq_of_dvd_sub hxy
  have hsum : m ∣ (y ^ 2 - x ^ 2) + (x ^ 2 - a) := dvd_add hsq hx
  convert hsum using 1
  ring

theorem isSquareMod_mul_of_isCoprime
    {m n a : _root_.Polynomial R} (hmn : IsCoprime m n)
    (hm : IsSquareMod m a) (hn : IsSquareMod n a) :
    IsSquareMod (m * n) a := by
  rcases hm with ⟨x, hx⟩
  rcases hn with ⟨y, hy⟩
  rcases hmn with ⟨s, t, hst⟩
  let z : _root_.Polynomial R := y * (s * m) + x * (t * n)
  have hxst : x * (s * m + t * n) = x := by rw [hst, mul_one]
  have hyst : y * (s * m + t * n) = y := by rw [hst, mul_one]
  have hzm : m ∣ z - x := by
    have : z - x = (y * s - x * s) * m := by
      calc
        z - x = y * (s * m) + x * (t * n) - x * (s * m + t * n) := by
          rw [hxst]
        _ = (y * s - x * s) * m := by ring
    rw [this]
    exact dvd_mul_left m _
  have hzn : n ∣ z - y := by
    have : z - y = (x * t - y * t) * n := by
      calc
        z - y = y * (s * m) + x * (t * n) - y * (s * m + t * n) := by
          rw [hyst]
        _ = (x * t - y * t) * n := by ring
    rw [this]
    exact dvd_mul_left n _
  refine ⟨z, IsCoprime.mul_dvd ⟨s, t, hst⟩ ?_ ?_⟩
  · exact polynomial_dvd_sq_sub_of_dvd_sub_of_dvd_sq_sub hzm hx
  · exact polynomial_dvd_sq_sub_of_dvd_sub_of_dvd_sq_sub hzn hy

theorem isSquareMod_finset_prod_of_pairwise_isCoprime
    {ι : Type*} {a : _root_.Polynomial R}
    (s : Finset ι) (m : ι → _root_.Polynomial R)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (m i) (m j))
    (hall : ∀ i ∈ s, IsSquareMod (m i) a) :
    IsSquareMod (∏ i ∈ s, m i) a := by
  classical
  revert hpair hall
  refine Finset.induction_on s ?_ ?_
  · intro _hpair _hall
    simpa using isSquareMod_one (R := R) a
  · intro b t hbt ih hpair_insert hall_insert
    rw [Finset.prod_insert hbt]
    refine isSquareMod_mul_of_isCoprime ?_ ?_ ?_
    · exact IsCoprime.prod_right fun i hit =>
        hpair_insert b (Finset.mem_insert_self b t) i (Finset.mem_insert_of_mem hit) (by
          intro hbi
          exact hbt (hbi ▸ hit))
    · exact hall_insert b (Finset.mem_insert_self b t)
    · exact ih
        (fun i hit j hjt hij =>
          hpair_insert i (Finset.mem_insert_of_mem hit) j (Finset.mem_insert_of_mem hjt) hij)
        (fun i hit => hall_insert i (Finset.mem_insert_of_mem hit))

theorem isSquareMod_prod_normalizedFactors_of_squarefree
    {R : Type*} [Field R] [DecidableEq R] {m a : _root_.Polynomial R}
    (hm0 : m ≠ 0) (hsq : Squarefree m)
    (hall :
      ∀ π : _root_.Polynomial R,
        π ∈ UniqueFactorizationMonoid.normalizedFactors m → IsSquareMod π a) :
    IsSquareMod (UniqueFactorizationMonoid.normalizedFactors m).prod a := by
  classical
  let S := (UniqueFactorizationMonoid.normalizedFactors m).toFinset
  have hnodup : (UniqueFactorizationMonoid.normalizedFactors m).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hm0).mp hsq
  have hval : S.val = UniqueFactorizationMonoid.normalizedFactors m := by
    have hfin := Multiset.toFinset_eq hnodup
    exact congrArg Finset.val hfin.symm
  have hS :
      IsSquareMod (∏ π ∈ S, π) a :=
    isSquareMod_finset_prod_of_pairwise_isCoprime
      S (fun π : _root_.Polynomial R => π)
      (fun π hπ ρ hρ hneq => by
        have hπ' : π ∈ UniqueFactorizationMonoid.normalizedFactors m := by
          exact Multiset.mem_toFinset.mp hπ
        have hρ' : ρ ∈ UniqueFactorizationMonoid.normalizedFactors m := by
          exact Multiset.mem_toFinset.mp hρ
        have hnotdvd : ¬ π ∣ ρ := by
          intro hdvd
          have heq :
              π = ρ :=
            UniqueFactorizationMonoid.normalizedFactors_eq_of_dvd m π hπ' ρ hρ' hdvd
          exact hneq heq
        exact
          (UniqueFactorizationMonoid.irreducible_of_normalized_factor π hπ').coprime_iff_not_dvd.mpr
            hnotdvd)
      (fun π hπ => hall π (Multiset.mem_toFinset.mp hπ))
  have hprod : (∏ π ∈ S, π) = (UniqueFactorizationMonoid.normalizedFactors m).prod := by
    change S.prod id = (UniqueFactorizationMonoid.normalizedFactors m).prod
    rw [← Finset.prod_val S, hval]
  simpa [hprod] using hS

theorem isSquareMod_of_forall_normalizedFactors_of_squarefree
    {R : Type*} [Field R] [DecidableEq R] {m a : _root_.Polynomial R}
    (hm0 : m ≠ 0) (hsq : Squarefree m)
    (hall :
      ∀ π : _root_.Polynomial R,
        π ∈ UniqueFactorizationMonoid.normalizedFactors m → IsSquareMod π a) :
    IsSquareMod m a :=
  (isSquareMod_prod_normalizedFactors_of_squarefree hm0 hsq hall).of_associated
    (UniqueFactorizationMonoid.prod_normalizedFactors hm0).symm

theorem isSquareMod_of_forall_irreducible_dvd_of_squarefree
    {R : Type*} [Field R] {m a : _root_.Polynomial R}
    (hm0 : m ≠ 0) (hsq : Squarefree m)
    (hall :
      ∀ π : _root_.Polynomial R,
        Irreducible π → π ∣ m → IsSquareMod π a) :
    IsSquareMod m a := by
  classical
  exact isSquareMod_of_forall_normalizedFactors_of_squarefree hm0 hsq
    (fun π hπ =>
      hall π
        (UniqueFactorizationMonoid.irreducible_of_normalized_factor π hπ)
        (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hπ))

theorem isSquareMod_X_sub_C_iff (a : R) (f : _root_.Polynomial R) :
    IsSquareMod (_root_.Polynomial.X - _root_.Polynomial.C a) f ↔
      IsSquare (f.eval a) := by
  constructor
  · rintro ⟨x, hx⟩
    have hroot : (x ^ 2 - f).IsRoot a :=
      (_root_.Polynomial.dvd_iff_isRoot).mp hx
    have heq : x.eval a ^ 2 - f.eval a = 0 := by
      simpa [_root_.Polynomial.IsRoot, map_pow] using hroot
    exact ⟨x.eval a, by simpa [pow_two] using (sub_eq_zero.mp heq).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨_root_.Polynomial.C x, ?_⟩
    rw [_root_.Polynomial.dvd_iff_isRoot, _root_.Polynomial.IsRoot]
    simp [hx, pow_two]

theorem isSquareMod_linear_associated_iff
    {π : _root_.Polynomial R} {a : R} {f : _root_.Polynomial R}
    (hπ : Associated π (_root_.Polynomial.X - _root_.Polynomial.C a)) :
    IsSquareMod π f ↔ IsSquare (f.eval a) := by
  rw [isSquareMod_associated_iff hπ]
  exact isSquareMod_X_sub_C_iff a f

theorem isSquareMod_linear_associated_of_nonneg_eval
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {π : _root_.Polynomial R} {a : R} {f : _root_.Polynomial R}
    (hπ : Associated π (_root_.Polynomial.X - _root_.Polynomial.C a)) (hf : 0 ≤ f.eval a) :
    IsSquareMod π f :=
  (isSquareMod_linear_associated_iff hπ).mpr (IsSquare.of_nonneg hf)

end RatFuncWittLocalGlobal
