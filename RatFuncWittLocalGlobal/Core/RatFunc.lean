/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Core.Basic

/-!
# Auxiliary lemmas for rational functions
-/

open scoped BigOperators

namespace RatFuncWittLocalGlobal

namespace RatFunc

variable {R ι : Type*}

theorem exists_common_denominator [Field R] [Finite ι] (x : ι → RatFunc R) :
    ∃ d : Polynomial R, d ≠ 0 ∧
      ∀ i, ∃ p : Polynomial R,
        x i = algebraMap (Polynomial R) (RatFunc R) p /
          algebraMap (Polynomial R) (RatFunc R) d := by
  classical
  let _ := Fintype.ofFinite ι
  let d : Polynomial R := ∏ i, (x i).denom
  have hd : d ≠ 0 := by
    simp [d, Finset.prod_ne_zero_iff, RatFunc.denom_ne_zero]
  refine ⟨d, hd, fun i => ?_⟩
  exact (RatFunc.denom_dvd (x := x i) hd).mp
    (Finset.dvd_prod_of_mem (fun i => (x i).denom) (Finset.mem_univ i))

end RatFunc

end RatFuncWittLocalGlobal
