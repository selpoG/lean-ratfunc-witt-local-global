/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal.Core.Basic

/-!
# Strict nonzero signs

The two strict signs and their elementary ordered-field API. This module is
independent of the polynomial and quadratic-form developments.
-/

namespace RatFuncWittLocalGlobal

universe u

/-- A strict nonzero sign. -/
inductive StrictSign where
  | pos
  | neg
  deriving DecidableEq

namespace StrictSign

/-- A value has the specified strict sign. -/
def Holds {R : Type u} [LinearOrder R] [Zero R]
    (s : StrictSign) (x : R) : Prop :=
  match s with
  | .pos => 0 < x
  | .neg => x < 0

/-- The opposite strict sign. -/
def opposite : StrictSign → StrictSign
  | .pos => .neg
  | .neg => .pos

end StrictSign
end RatFuncWittLocalGlobal
