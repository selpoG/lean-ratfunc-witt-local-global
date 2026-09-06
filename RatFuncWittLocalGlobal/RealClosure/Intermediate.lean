/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Order.Ring.Ordering.Defs
import Mathlib.Order.Zorn
import RatFuncWittLocalGlobal.Ordering.Basic

/-!
# Ordered intermediate fields inside an algebraic closure

The algebraic closure itself is not orderable.  In an ordered real-closure
construction one therefore keeps an order only on an intermediate field and
records it by its nonnegative cone in the ambient algebraic closure.  This
file supplies that small, concrete foundation; the later maximality argument
still has to adjoin roots while extending the cone.
-/

namespace RatFuncWittLocalGlobal

namespace OrderedRealClosure

universe u

open Polynomial
open Module

variable (F : Type u) [Field F] [LinearOrder F] [IsStrictOrderedRing F]

local notation "Ω" => AlgebraicClosure F

/--
An ordered intermediate field in `Ω`.

`nonnegative` is an ambient cone.  The closure axioms are stated in the
ambient field but only involve elements of the cone (and hence, by
`nonnegative_subset`, elements of the intermediate field).  `total` and
`proper` are the order axioms on the carrier.  `base_nonnegative` says that
the cone restricts to the given ordering on the base field.
-/
structure Intermediate where
  carrier : IntermediateField F Ω
  nonnegative : Set Ω
  nonnegative_subset : nonnegative ⊆ carrier
  zero_mem : (0 : Ω) ∈ nonnegative
  one_mem : (1 : Ω) ∈ nonnegative
  add_mem : ∀ {x y : Ω}, x ∈ nonnegative → y ∈ nonnegative → x + y ∈ nonnegative
  mul_mem : ∀ {x y : Ω}, x ∈ nonnegative → y ∈ nonnegative → x * y ∈ nonnegative
  square_mem : ∀ {x : Ω}, x ∈ carrier → x ^ 2 ∈ nonnegative
  total : ∀ {x : Ω}, x ∈ carrier → x ∈ nonnegative ∨ -x ∈ nonnegative
  proper : (-1 : Ω) ∉ nonnegative
  base_nonnegative : ∀ x : F, (0 : F) ≤ x ↔ algebraMap F Ω x ∈ nonnegative

/-- The cone of an ordered intermediate field, viewed on its subtype. -/
def ambientConePreordering {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (E : Intermediate F) : RingPreordering E.carrier where
  carrier := {x : E.carrier | (x : AlgebraicClosure F) ∈ E.nonnegative}
  zero_mem' := by simpa using E.zero_mem
  one_mem' := by simpa using E.one_mem
  add_mem' := by
    intro x y hx hy
    simpa using E.add_mem hx hy
  mul_mem' := by
    intro x y hx hy
    simpa using E.mul_mem hx hy
  mem_of_isSquare' := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    simpa [pow_two] using E.square_mem y.property
  neg_one_notMem' := by
    intro h
    exact E.proper h

@[simp] theorem mem_ambientConePreordering {F : Type u} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {E : Intermediate F} {x : E.carrier} :
    x ∈ ambientConePreordering E ↔ (x : AlgebraicClosure F) ∈ E.nonnegative :=
  Iff.rfl

/-- Totality of an ambient cone makes its subtype preordering an ordering. -/
theorem ambientConePreordering_isOrdering {F : Type u} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (E : Intermediate F) :
    (ambientConePreordering E).IsOrdering := by
  rw [RingPreordering.isOrdering_iff]
  intro a b hab
  by_cases ha : a ∈ ambientConePreordering E
  · exact Or.inl ha
  by_cases hb : b ∈ ambientConePreordering E
  · exact Or.inr hb
  have ha' : (a : AlgebraicClosure F) ∉ E.nonnegative := by
    intro ha'
    exact ha ((mem_ambientConePreordering (E := E)).2 ha')
  have hb' : (b : AlgebraicClosure F) ∉ E.nonnegative := by
    intro hb'
    exact hb ((mem_ambientConePreordering (E := E)).2 hb')
  have hna : -a ∈ ambientConePreordering E := by
    apply (mem_ambientConePreordering (E := E)).2
    simpa using (E.total a.property).resolve_left ha'
  have hnb : -b ∈ ambientConePreordering E := by
    apply (mem_ambientConePreordering (E := E)).2
    simpa using (E.total b.property).resolve_left hb'
  have hab' : a * b ∈ ambientConePreordering E := by
    simpa only [neg_mul_neg] using mul_mem hna hnb
  have hz : a * b = 0 :=
    RingPreordering.eq_zero_of_mem_of_neg_mem hab' hab
  rcases mul_eq_zero.mp hz with ha0 | hb0
  · left
    simpa only [ha0] using (zero_mem (ambientConePreordering E))
  · right
    simpa only [hb0] using (zero_mem (ambientConePreordering E))

attribute [instance] ambientConePreordering_isOrdering

/-- The order induced on the carrier by the ambient cone. -/
noncomputable instance instLinearOrder (E : Intermediate F) : LinearOrder E.carrier := by
  exact RingPreordering.linearOrderOfIsOrdering (ambientConePreordering E)

/-- The strict ordered-ring structure induced on the carrier by the ambient cone. -/
noncomputable instance instIsStrictOrderedRing (E : Intermediate F) :
    IsStrictOrderedRing E.carrier := by
  exact RingPreordering.isStrictOrderedRingOfIsOrdering (ambientConePreordering E)

theorem base_nonnegative_iff (E : Intermediate F) (x : F) :
    0 ≤ x ↔ 0 ≤ algebraMap F E.carrier x := by
  calc
    0 ≤ x ↔ algebraMap F E.carrier x ∈ ambientConePreordering E := by
      simpa [ambientConePreordering] using E.base_nonnegative x
    _ ↔ 0 ≤ algebraMap F E.carrier x := by
      exact (RingPreordering.zero_le_linearOrderOfIsOrdering_iff
        (ambientConePreordering E)).symm

/-!
### Inclusion order

An extension must preserve the old cone on the old carrier.  This is exactly
the compatibility needed for taking unions of chains later.
-/

/-- The cone compatibility condition along an inclusion of carriers. -/
def ConeCompatible {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (E E' : Intermediate F) (_h : E.carrier ≤ E'.carrier) : Prop :=
  ∀ {x : AlgebraicClosure F}, x ∈ E.carrier →
    (x ∈ E.nonnegative ↔ x ∈ E'.nonnegative)

/-- Inclusion of ordered intermediate fields. -/
def orderedLe {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (E E' : Intermediate F) : Prop :=
  ∃ h : E.carrier ≤ E'.carrier, ConeCompatible (F := F) E E' h

theorem orderedLe_refl (E : Intermediate F) : orderedLe E E := by
  refine ⟨le_rfl, ?_⟩
  intro x hx
  exact Iff.rfl

theorem orderedLe_trans {E E' E'' : Intermediate F}
    (h₁ : orderedLe E E') (h₂ : orderedLe E' E'') : orderedLe E E'' := by
  rcases h₁ with ⟨h₁, h₁cone⟩
  rcases h₂ with ⟨h₂, h₂cone⟩
  have hcar : E.carrier ≤ E''.carrier :=
    @Preorder.le_trans (IntermediateField F (AlgebraicClosure F))
      (inferInstance : Preorder (IntermediateField F (AlgebraicClosure F)))
      E.carrier E'.carrier E''.carrier h₁ h₂
  refine ⟨hcar, ?_⟩
  intro x hx
  exact (h₁cone hx).trans (h₂cone (h₁ hx))

theorem orderedLe_antisymm {E E' : Intermediate F}
    (h₁ : orderedLe E E') (h₂ : orderedLe E' E) : E = E' := by
  rcases h₁ with ⟨h₁, h₁cone⟩
  rcases h₂ with ⟨h₂, h₂cone⟩
  have hcarrier : E.carrier = E'.carrier :=
    @PartialOrder.le_antisymm (IntermediateField F (AlgebraicClosure F))
      (inferInstance : PartialOrder (IntermediateField F (AlgebraicClosure F)))
      E.carrier E'.carrier h₁ h₂
  cases E with
  | mk E P hP hzero hone hadd hmul hsq htotal hproper hbase =>
    cases E' with
    | mk E' P' hP' hzero' hone' hadd' hmul' hsq' htotal' hproper' hbase' =>
      dsimp at hcarrier h₁ h₂ h₁cone h₂cone ⊢
      cases hcarrier
      have hcone : P = P' := by
        ext x
        by_cases hx : x ∈ E
        · exact h₁cone hx
        · constructor
          · intro hp
            exact (hx (hP hp)).elim
          · intro hp
            exact (hx (hP' hp)).elim
      cases hcone
      rfl

instance instPartialOrderIntermediate : PartialOrder (Intermediate F) where
  le := orderedLe
  le_refl := @orderedLe_refl F _ _ _
  le_trans := @orderedLe_trans F _ _ _
  le_antisymm := @orderedLe_antisymm F _ _ _

omit [IsStrictOrderedRing F] in
theorem intermediate_is_algebraic (E : Intermediate F) :
    Algebra.IsAlgebraic F E.carrier := by
  infer_instance

theorem base_positive (E : Intermediate F) {x : F} (hx : 0 < x) :
    0 < algebraMap F E.carrier x := by
  have hnonneg : 0 ≤ algebraMap F E.carrier x :=
    (base_nonnegative_iff (F := F) E x).mp hx.le
  apply lt_of_le_of_ne hnonneg
  intro hzero
  have hxzero : x = 0 := by
    apply (RingHom.injective (algebraMap F E.carrier))
    simpa using hzero.symm
  exact (ne_of_gt hx) hxzero

/-!
### Algebraic adjunction groundwork

The following carrier operation is independent of any attempted extension of
the cone.  It is the ordinary field obtained by adjoining one element of the
algebraic closure, then viewed again as an `F`-intermediate field.
-/

noncomputable def adjoinCarrier {F : Type u} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (E : Intermediate F) (α : AlgebraicClosure F) :
    IntermediateField F (AlgebraicClosure F) :=
  IntermediateField.restrictScalars F
    (IntermediateField.adjoin E.carrier ({α} : Set (AlgebraicClosure F)))

theorem adjoin_mem_adjoinCarrier (E : Intermediate F) (α : Ω) :
    α ∈ adjoinCarrier E α := by
  change α ∈ IntermediateField.adjoin E.carrier ({α} : Set Ω)
  exact IntermediateField.mem_adjoin_of_mem E.carrier (Set.mem_singleton α)

omit [IsStrictOrderedRing F] in
theorem alpha_integral (E : Intermediate F) {a : E.carrier} {α : Ω}
    (hα : α ^ 2 = (a : Ω)) :
    IsIntegral E.carrier α := by
  refine ⟨X ^ 2 - C a, ?_, ?_⟩
  · exact monic_X_pow_sub_C a (by norm_num)
  · rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    exact sub_eq_zero.mpr hα

omit [IsStrictOrderedRing F] in
theorem minpoly_alpha_eq (E : Intermediate F) {a : E.carrier} {α : Ω}
    (hα : α ^ 2 = (a : Ω)) (hnsq : ¬ IsSquare a) :
    minpoly E.carrier α = X ^ 2 - C a := by
  have hi : IsIntegral E.carrier α := alpha_integral F E hα
  have hirr : Irreducible (X ^ 2 - C a) := by
    apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro b hb
    apply hnsq
    exact ⟨b, by simpa [pow_two] using hb.symm⟩
  apply (minpoly.eq_of_irreducible_of_monic hirr ?_
    (monic_X_pow_sub_C a (by norm_num))).symm
  rw [aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  exact sub_eq_zero.mpr hα

omit [IsStrictOrderedRing F] in
theorem exists_linear_representation (E : Intermediate F) {a : E.carrier} {α : Ω}
    (hα : α ^ 2 = (a : Ω)) (hnsq : ¬ IsSquare a)
    (z : IntermediateField.adjoin E.carrier ({α} : Set Ω)) :
    ∃ x y : E.carrier, (z : Ω) = (x : Ω) + (y : Ω) * α := by
  let pb := IntermediateField.adjoin.powerBasis (alpha_integral F E hα)
  have hmin := minpoly_alpha_eq F E hα hnsq
  have hdim : pb.dim = 2 := by
    dsimp [pb, IntermediateField.adjoin.powerBasis]
    simp [hmin]
  have hgen : (pb.gen : Ω) = α := by
    rfl
  let b : Basis (Fin 2) E.carrier
      (IntermediateField.adjoin E.carrier ({α} : Set Ω)) :=
    pb.basis.reindex (finCongr hdim)
  let x : E.carrier := b.repr z 0
  let y : E.carrier := b.repr z 1
  refine ⟨x, y, ?_⟩
  have hb (i : Fin 2) : b i = pb.gen ^ (i : Nat) := by
    simp [b, Basis.reindex_apply, pb.basis_eq_pow]
  have hz' : z = x • b 0 + y • b 1 := by
    rw [← b.sum_repr z, Fin.sum_univ_two]
  have hb0 : b 0 = 1 := by simpa using hb 0
  have hb1 : b 1 = pb.gen := by simpa using hb 1
  rw [hz', hb0, hb1]
  change ((x • (1 : IntermediateField.adjoin E.carrier ({α} : Set Ω)) + y • pb.gen :
    IntermediateField.adjoin E.carrier ({α} : Set Ω)) : Ω) = _
  simp only [Algebra.smul_def, mul_one]
  change (x : Ω) + (y : Ω) * (pb.gen : Ω) = _
  rw [hgen]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem exists_square_root (a : Ω) : ∃ α : Ω, α ^ 2 = a := by
  simpa using IsAlgClosed.exists_pow_nat_eq a (n := 2) (by norm_num)

omit [IsStrictOrderedRing F] in
theorem exists_root_over_intermediate (E : Intermediate F) {p : E.carrier[X]}
    (hp : p.degree ≠ 0) :
    ∃ α : Ω, Polynomial.eval₂ (algebraMap E.carrier Ω) α p = 0 := by
  have hmapdeg : (p.map (algebraMap E.carrier Ω)).degree ≠ 0 := by
    simpa [Polynomial.degree_map_eq_of_injective
      (RingHom.injective (algebraMap E.carrier Ω))] using hp
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root
    (p.map (algebraMap E.carrier Ω)) hmapdeg
  exact ⟨α, by simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using hα⟩

theorem maximal_eq_of_le {M E' : Intermediate F} (hmax : IsMax M) (hME : M ≤ E') :
    E' = M := by
  exact le_antisymm (hmax hME) hME

theorem maximal_contains_of_le {M E' : Intermediate F} (hmax : IsMax M)
    (hME : M ≤ E') {α : Ω} (hα : α ∈ E'.carrier) : α ∈ M.carrier := by
  have hEq : E' = M := maximal_eq_of_le (F := F) hmax hME
  simpa [hEq] using hα

/-- The ambient image of the nonnegative cone of `F`. -/
def baseCone : Set Ω := {x | ∃ y : F, 0 ≤ y ∧ algebraMap F Ω y = x}

omit [IsStrictOrderedRing F] in
/-- The bottom ordered intermediate field. -/
noncomputable def base : Intermediate F where
  carrier := ⊥
  nonnegative := baseCone F
  nonnegative_subset := by
    intro x hx
    rcases hx with ⟨y, _, rfl⟩
    exact (IntermediateField.mem_bot).2 ⟨y, rfl⟩
  zero_mem := by
    exact ⟨0, le_rfl, by simp⟩
  one_mem := by
    exact ⟨1, by simp, by simp⟩
  add_mem := by
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a + b, add_nonneg ha hb, ?_⟩
    simp
  mul_mem := by
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a * b, mul_nonneg ha hb, ?_⟩
    simp
  square_mem := by
    intro x hx
    rcases (IntermediateField.mem_bot).1 hx with ⟨a, rfl⟩
    refine ⟨a ^ 2, sq_nonneg a, ?_⟩
    simp [pow_two]
  total := by
    intro x hx
    rcases (IntermediateField.mem_bot).1 hx with ⟨a, rfl⟩
    rcases le_total 0 a with ha | ha
    · exact Or.inl ⟨a, ha, rfl⟩
    · right
      refine ⟨-a, ?_, ?_⟩
      · exact neg_nonneg.mpr ha
      · simp
  proper := by
    intro h
    rcases h with ⟨a, ha, hmap⟩
    have ha' : a = -1 := by
      apply (RingHom.injective (algebraMap F Ω))
      simpa using hmap
    subst ha'
    norm_num at ha
  base_nonnegative := by
    intro x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      have : y = x := by
        apply (RingHom.injective (algebraMap F Ω))
        simpa using hxy
      simpa [this] using hy

theorem chain_carrier_directed {s : Set (Intermediate F)}
    (hs : IsChain (· ≤ ·) s) :
    Directed (· ≤ ·) (fun E : s => E.1.carrier) := by
  intro E E'
  rcases hs.total E.2 E'.2 with hEE' | hE'E
  · rcases hEE' with ⟨h, _⟩
    exact ⟨E', h, le_rfl⟩
  · rcases hE'E with ⟨h, _⟩
    exact ⟨E, le_rfl, h⟩

theorem chain_upperBound {s : Set (Intermediate F)} (hne : s.Nonempty)
    (hs : IsChain (· ≤ ·) s) :
    ∃ U : Intermediate F, ∀ E ∈ s, E ≤ U := by
  let _ : Nonempty s := hne.to_subtype
  let t : s → IntermediateField F Ω := fun E ↦ E.1.carrier
  let hdir : Directed (· ≤ ·) t := by
    simpa [t] using chain_carrier_directed (F := F) hs
  let Ucarrier : IntermediateField F Ω := ⨆ i : s, t i
  let Ucone : Set Ω := ⋃ i : s, (i.1.nonnegative : Set Ω)
  have hUcarrier : (Ucarrier : Set Ω) = ⋃ i : s, (t i : Set Ω) := by
    exact IntermediateField.coe_iSup_of_directed hdir
  have mem_Ucarrier_of_mem (i : s) {x : Ω} (hx : x ∈ i.1.carrier) :
      x ∈ Ucarrier := by
    change x ∈ (Ucarrier : Set Ω)
    rw [hUcarrier]
    exact Set.mem_iUnion.2 ⟨i, hx⟩
  have mem_chain_of_mem_Ucarrier {x : Ω} (hx : x ∈ Ucarrier) :
      ∃ i : s, x ∈ i.1.carrier := by
    change x ∈ (Ucarrier : Set Ω) at hx
    rw [hUcarrier] at hx
    exact Set.mem_iUnion.1 hx
  have hcone_subset : Ucone ⊆ Ucarrier := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
    exact mem_Ucarrier_of_mem i (i.1.nonnegative_subset hxi)
  have hzero : (0 : Ω) ∈ Ucone := by
    obtain ⟨i, _⟩ := hne
    exact Set.mem_iUnion.2 ⟨⟨i, ‹i ∈ s›⟩, (⟨i, ‹i ∈ s›⟩ : s).1.zero_mem⟩
  have hone : (1 : Ω) ∈ Ucone := by
    obtain ⟨i, _⟩ := hne
    exact Set.mem_iUnion.2 ⟨⟨i, ‹i ∈ s›⟩, (⟨i, ‹i ∈ s›⟩ : s).1.one_mem⟩
  have hadd : ∀ {x y : Ω}, x ∈ Ucone → y ∈ Ucone → x + y ∈ Ucone := by
    intro x y hx hy
    rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
    rcases Set.mem_iUnion.1 hy with ⟨j, hyj⟩
    rcases hs.total i.2 j.2 with hij | hji
    · rcases hij with ⟨hij, hcompat⟩
      have hxj : x ∈ j.1.nonnegative := (hcompat (i.1.nonnegative_subset hxi)).mp hxi
      exact Set.mem_iUnion.2 ⟨j, j.1.add_mem hxj hyj⟩
    · rcases hji with ⟨hji, hcompat⟩
      have hyi : y ∈ i.1.nonnegative := (hcompat (j.1.nonnegative_subset hyj)).mp hyj
      exact Set.mem_iUnion.2 ⟨i, i.1.add_mem hxi hyi⟩
  have hmul : ∀ {x y : Ω}, x ∈ Ucone → y ∈ Ucone → x * y ∈ Ucone := by
    intro x y hx hy
    rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
    rcases Set.mem_iUnion.1 hy with ⟨j, hyj⟩
    rcases hs.total i.2 j.2 with hij | hji
    · rcases hij with ⟨hij, hcompat⟩
      have hxj : x ∈ j.1.nonnegative := (hcompat (i.1.nonnegative_subset hxi)).mp hxi
      exact Set.mem_iUnion.2 ⟨j, j.1.mul_mem hxj hyj⟩
    · rcases hji with ⟨hji, hcompat⟩
      have hyi : y ∈ i.1.nonnegative := (hcompat (j.1.nonnegative_subset hyj)).mp hyj
      exact Set.mem_iUnion.2 ⟨i, i.1.mul_mem hxi hyi⟩
  have hsq : ∀ {x : Ω}, x ∈ Ucarrier → x ^ 2 ∈ Ucone := by
    intro x hx
    rcases mem_chain_of_mem_Ucarrier hx with ⟨i, hxi⟩
    exact Set.mem_iUnion.2 ⟨i, i.1.square_mem hxi⟩
  have htotal : ∀ {x : Ω}, x ∈ Ucarrier → x ∈ Ucone ∨ -x ∈ Ucone := by
    intro x hx
    rcases mem_chain_of_mem_Ucarrier hx with ⟨i, hxi⟩
    rcases i.1.total hxi with hxi | hxi
    · exact Or.inl (Set.mem_iUnion.2 ⟨i, hxi⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨i, hxi⟩)
  have hproper : (-1 : Ω) ∉ Ucone := by
    intro h
    rcases Set.mem_iUnion.1 h with ⟨i, hi⟩
    exact i.1.proper hi
  let U : Intermediate F :=
    { carrier := Ucarrier
      nonnegative := Ucone
      nonnegative_subset := hcone_subset
      zero_mem := hzero
      one_mem := hone
      add_mem := hadd
      mul_mem := hmul
      square_mem := hsq
      total := htotal
      proper := hproper
      base_nonnegative := by
        intro x
        constructor
        · intro hx
          obtain ⟨i, _⟩ := hne
          exact Set.mem_iUnion.2 ⟨⟨i, ‹i ∈ s›⟩, ((⟨i, ‹i ∈ s›⟩ : s).1.base_nonnegative x).mp hx⟩
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
          exact ((i.1.base_nonnegative x).mpr hxi) }
  refine ⟨U, ?_⟩
  intro E hE
  let i : s := ⟨E, hE⟩
  refine ⟨?_, ?_⟩
  · exact le_iSup t i
  · intro x hx
    constructor
    · intro hxn
      exact Set.mem_iUnion.2 ⟨i, hxn⟩
    · intro hxn
      rcases Set.mem_iUnion.1 hxn with ⟨j, hj⟩
      rcases hs.total i.2 j.2 with hij | hji
      · rcases hij with ⟨_, hcompat⟩
        exact (hcompat hx).mpr hj
      · rcases hji with ⟨_, hcompat⟩
        exact (hcompat (j.1.nonnegative_subset hj)).mp hj

/-!
Zorn's lemma now applies to the cone-compatible ordered intermediate fields
above the seed.  This is only the maximal ordered-subfield stage; adjoining a
root while extending the cone is the separate real-closure step.
-/

theorem exists_maximal_orderedIntermediate :
    ∃ M : Intermediate F, base F ≤ M ∧ IsMax M := by
  obtain ⟨M, hbaseM, hmaxM⟩ :=
    zorn_le_nonempty_Ici₀ (base F)
      (fun c _ hc y hy => by
        obtain ⟨U, hU⟩ := chain_upperBound (F := F) ⟨y, hy⟩ hc
        exact ⟨U, hU⟩)
      (base F) le_rfl
  exact ⟨M, hbaseM, hmaxM⟩

theorem exists_maximal_ordered_algebraic_extension :
    ∃ M : Intermediate F,
      base F ≤ M ∧ IsMax M ∧ Algebra.IsAlgebraic F M.carrier ∧
        (∀ x : F, 0 < x → 0 < algebraMap F M.carrier x) := by
  obtain ⟨M, hbaseM, hmaxM⟩ := exists_maximal_orderedIntermediate (F := F)
  exact ⟨M, hbaseM, hmaxM, intermediate_is_algebraic (F := F) M,
    fun x hx => base_positive (F := F) M hx⟩

end OrderedRealClosure

end RatFuncWittLocalGlobal
