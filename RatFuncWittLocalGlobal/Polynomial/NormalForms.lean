/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
# Small-degree and quartic polynomial normal forms

This file contains polynomial algebra helpers used by the local-global
reduction.  They are kept separate from the main reduction file so changes to
the later arithmetic layers do not force these low-level normal forms to be
re-elaborated.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u

theorem Polynomial.eq_C_add_C_mul_X_of_natDegree_lt_two
    {R : Type u} [Semiring R] {P : Polynomial R} (hdeg : P.natDegree < 2) :
    P = Polynomial.C (P.coeff 0) + Polynomial.C (P.coeff 1) * Polynomial.X := by
  have hle : P.natDegree ≤ 1 := by omega
  calc
    P = Polynomial.C (P.coeff 1) * Polynomial.X + Polynomial.C (P.coeff 0) :=
      Polynomial.eq_X_add_C_of_natDegree_le_one hle
    _ = Polynomial.C (P.coeff 0) + Polynomial.C (P.coeff 1) * Polynomial.X := by
      rw [add_comm]

end RatFunc
end RatFuncWittLocalGlobal
