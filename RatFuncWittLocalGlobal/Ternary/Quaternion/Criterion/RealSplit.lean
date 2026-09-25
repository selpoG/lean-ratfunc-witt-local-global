/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Ternary.QuaternionSymbol
import RatFuncWittLocalGlobal.Ordering.Obstruction

/-!
# RatFunc Quaternion-Symbol Criterion Core

This file contains the Legendre-independent residue criterion interface for
quaternion symbols over `RatFunc R`.
-/

namespace RatFuncWittLocalGlobal

universe u v

variable {R : Type u}

/--
The quaternion symbol `(u, v)` over `RatFunc R` is split after every ordered
real-closed extension of `RatFunc R`.
-/
def RatFuncQuaternionRealSplit [Field R] (u v : RatFunc R) : Prop :=
  ∀ {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
      [Algebra (RatFunc R) K],
    QuaternionSymbolSplit (algebraMap (RatFunc R) K u) (algebraMap (RatFunc R) K v)

/-- Real split is symmetric in the two quaternion-symbol coefficients. -/
theorem ratFuncQuaternionRealSplit_comm [Field R] {p q : RatFunc R} :
    RatFuncQuaternionRealSplit.{u, v} p q ↔
      RatFuncQuaternionRealSplit.{u, v} q p := by
  constructor
  · intro h K hKField hKOrder hKStrict hKRealClosed hKAlg
    let _ : Field K := hKField
    let _ : LinearOrder K := hKOrder
    let _ : IsStrictOrderedRing K := hKStrict
    let _ : IsRealClosed K := hKRealClosed
    let _ : Algebra (RatFunc R) K := hKAlg
    exact quaternionSymbolSplit_comm.mp (h (K := K))
  · intro h K hKField hKOrder hKStrict hKRealClosed hKAlg
    let _ : Field K := hKField
    let _ : LinearOrder K := hKOrder
    let _ : IsStrictOrderedRing K := hKStrict
    let _ : IsRealClosed K := hKRealClosed
    let _ : Algebra (RatFunc R) K := hKAlg
    exact quaternionSymbolSplit_comm.mp (h (K := K))

/--
Real split is invariant under multiplying the first coefficient by a nonzero
square in `RatFunc R`.
-/
theorem ratFuncQuaternionRealSplit_mul_square_left
    [Field R] {p q s : RatFunc R} (hs : s ≠ 0) :
    RatFuncQuaternionRealSplit.{u, v} (p * s ^ 2) q ↔
      RatFuncQuaternionRealSplit.{u, v} p q := by
  constructor
  · intro h K hKField hKOrder hKStrict hKRealClosed hKAlg
    let _ : Field K := hKField
    let _ : LinearOrder K := hKOrder
    let _ : IsStrictOrderedRing K := hKStrict
    let _ : IsRealClosed K := hKRealClosed
    let _ : Algebra (RatFunc R) K := hKAlg
    let φ := algebraMap (RatFunc R) K
    have hsK : φ s ≠ 0 := by
      intro hzero
      exact hs ((algebraMap (RatFunc R) K).injective (by simpa [φ] using hzero))
    have hsplit :
        QuaternionSymbolSplit
          (φ p * φ s ^ 2)
          (φ q) := by
      simpa [φ, map_mul, map_pow] using h (K := K)
    exact (quaternionSymbolSplit_mul_square_left hsK).mp hsplit
  · intro h K hKField hKOrder hKStrict hKRealClosed hKAlg
    let _ : Field K := hKField
    let _ : LinearOrder K := hKOrder
    let _ : IsStrictOrderedRing K := hKStrict
    let _ : IsRealClosed K := hKRealClosed
    let _ : Algebra (RatFunc R) K := hKAlg
    let φ := algebraMap (RatFunc R) K
    have hsK : φ s ≠ 0 := by
      intro hzero
      exact hs ((algebraMap (RatFunc R) K).injective (by simpa [φ] using hzero))
    have hsplit :
        QuaternionSymbolSplit
          (φ p)
          (φ q) :=
      h (K := K)
    have hsplit' :
        QuaternionSymbolSplit
          (φ p * φ s ^ 2)
          (φ q) :=
      (quaternionSymbolSplit_mul_square_left hsK).mpr hsplit
    simpa [φ, map_mul, map_pow] using hsplit'

/--
Real split is invariant under multiplying the second coefficient by a nonzero
square in `RatFunc R`.
-/
theorem ratFuncQuaternionRealSplit_mul_square_right
    [Field R] {p q s : RatFunc R} (hs : s ≠ 0) :
    RatFuncQuaternionRealSplit.{u, v} p (q * s ^ 2) ↔
      RatFuncQuaternionRealSplit.{u, v} p q := by
  calc
    RatFuncQuaternionRealSplit.{u, v} p (q * s ^ 2) ↔
        RatFuncQuaternionRealSplit.{u, v} (q * s ^ 2) p :=
      ratFuncQuaternionRealSplit_comm
    _ ↔ RatFuncQuaternionRealSplit.{u, v} q p :=
      ratFuncQuaternionRealSplit_mul_square_left hs
    _ ↔ RatFuncQuaternionRealSplit.{u, v} p q :=
      ratFuncQuaternionRealSplit_comm

/--
Real split is invariant under multiplying the second coefficient by a nonzero
norm from `(RatFunc R)[√p]`.
-/
theorem ratFuncQuaternionRealSplit_mul_norm_right
    [Field R] {p q n α β : RatFunc R}
    (hn : n = α ^ 2 - p * β ^ 2) (hn0 : n ≠ 0) :
    RatFuncQuaternionRealSplit.{u, v} p (q * n) ↔
      RatFuncQuaternionRealSplit.{u, v} p q := by
  constructor
  · intro h K hKField hKOrder hKStrict hKRealClosed hKAlg
    let _ : Field K := hKField
    let _ : LinearOrder K := hKOrder
    let _ : IsStrictOrderedRing K := hKStrict
    let _ : IsRealClosed K := hKRealClosed
    let _ : Algebra (RatFunc R) K := hKAlg
    let φ := algebraMap (RatFunc R) K
    have hnK : φ n = φ α ^ 2 - φ p * φ β ^ 2 := by
      simpa [φ, map_mul, map_pow] using congrArg φ hn
    have hn0K : φ n ≠ 0 := by
      intro hzero
      exact hn0 ((algebraMap (RatFunc R) K).injective (by simpa [φ] using hzero))
    have hsplit : QuaternionSymbolSplit (φ p) (φ q * φ n) := by
      simpa [φ, map_mul] using h (K := K)
    exact (quaternionSymbolSplit_mul_norm_right_iff hnK hn0K).mp hsplit
  · intro h K hKField hKOrder hKStrict hKRealClosed hKAlg
    let _ : Field K := hKField
    let _ : LinearOrder K := hKOrder
    let _ : IsStrictOrderedRing K := hKStrict
    let _ : IsRealClosed K := hKRealClosed
    let _ : Algebra (RatFunc R) K := hKAlg
    let φ := algebraMap (RatFunc R) K
    have hnK : φ n = φ α ^ 2 - φ p * φ β ^ 2 := by
      simpa [φ, map_mul, map_pow] using congrArg φ hn
    have hn0K : φ n ≠ 0 := by
      intro hzero
      exact hn0 ((algebraMap (RatFunc R) K).injective (by simpa [φ] using hzero))
    have hsplit : QuaternionSymbolSplit (φ p) (φ q) :=
      h (K := K)
    have hsplit' : QuaternionSymbolSplit (φ p) (φ q * φ n) :=
      (quaternionSymbolSplit_mul_norm_right_iff hnK hn0K).mpr hsplit
    simpa [φ, map_mul] using hsplit'

/--
Real split is invariant under multiplying the first coefficient by a nonzero
norm from `(RatFunc R)[√q]`.
-/
theorem ratFuncQuaternionRealSplit_mul_norm_left
    [Field R] {p q n α β : RatFunc R}
    (hn : n = α ^ 2 - q * β ^ 2) (hn0 : n ≠ 0) :
    RatFuncQuaternionRealSplit.{u, v} (p * n) q ↔
      RatFuncQuaternionRealSplit.{u, v} p q := by
  calc
    RatFuncQuaternionRealSplit.{u, v} (p * n) q ↔
        RatFuncQuaternionRealSplit.{u, v} q (p * n) :=
      ratFuncQuaternionRealSplit_comm
    _ ↔ RatFuncQuaternionRealSplit.{u, v} q p :=
      ratFuncQuaternionRealSplit_mul_norm_right hn hn0
    _ ↔ RatFuncQuaternionRealSplit.{u, v} p q :=
      ratFuncQuaternionRealSplit_comm

/--
Two quaternion symbols over `RatFunc R` are the same up to independent nonzero
square factors on the two coefficients.
-/
def RatFuncQuaternionSquareClass [Field R]
    (p q p' q' : RatFunc R) : Prop :=
  ∃ s t : RatFunc R,
    s ≠ 0 ∧ t ≠ 0 ∧
      p = p' * s ^ 2 ∧ q = q' * t ^ 2

/-- A square-class relation transfers split from the representative back. -/
theorem ratFuncQuaternionSquareClass_transfers_split
    [Field R] {p q p' q' : RatFunc R}
    (hclass : RatFuncQuaternionSquareClass p q p' q') :
    QuaternionSymbolSplit p' q' → QuaternionSymbolSplit p q := by
  intro hsplit
  rcases hclass with ⟨s, t, hs, ht, rfl, rfl⟩
  exact
    (quaternionSymbolSplit_mul_square_right
      (u := p' * s ^ 2) (v := q') (s := t) ht).mpr
      ((quaternionSymbolSplit_mul_square_left
        (u := p') (v := q') (s := s) hs).mpr hsplit)

/--
A square-class relation transfers real split from the original symbol to the
representative.
-/
theorem ratFuncQuaternionSquareClass_transfers_realSplit
    [Field R] {p q p' q' : RatFunc R}
    (hclass : RatFuncQuaternionSquareClass p q p' q') :
    RatFuncQuaternionRealSplit.{u, v} p q →
      RatFuncQuaternionRealSplit.{u, v} p' q' := by
  intro hreal
  rcases hclass with ⟨s, t, hs, ht, rfl, rfl⟩
  intro K hKField hKOrder hKStrict hKRealClosed hKAlg
  let _ : Field K := hKField
  let _ : LinearOrder K := hKOrder
  let _ : IsStrictOrderedRing K := hKStrict
  let _ : IsRealClosed K := hKRealClosed
  let _ : Algebra (RatFunc R) K := hKAlg
  let φ := algebraMap (RatFunc R) K
  have hsK : φ s ≠ 0 := by
    intro hzero
    exact hs ((algebraMap (RatFunc R) K).injective (by simpa [φ] using hzero))
  have htK : φ t ≠ 0 := by
    intro hzero
    exact ht ((algebraMap (RatFunc R) K).injective (by simpa [φ] using hzero))
  have hsplit :
      QuaternionSymbolSplit (φ p' * φ s ^ 2) (φ q' * φ t ^ 2) := by
    simpa [φ, map_mul, map_pow] using hreal (K := K)
  have hsplit_right :
      QuaternionSymbolSplit (φ p' * φ s ^ 2) (φ q') :=
    (quaternionSymbolSplit_mul_square_right
      (u := φ p' * φ s ^ 2) (v := φ q') (s := φ t) htK).mp hsplit
  exact
    (quaternionSymbolSplit_mul_square_left
      (u := φ p') (v := φ q') (s := φ s) hsK).mp hsplit_right

end RatFuncWittLocalGlobal
