/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal

/-!
# Public axiom audit

Check that the primary diagonal and quadratic-form endpoints use only the standard axioms.
-/

/--
info: 'RatFuncWittLocalGlobal.diagonal_isotropic_iff_not_finiteSameStrictSignOrdering_of_card_ge_three_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RatFuncWittLocalGlobal.diagonal_isotropic_iff_not_finiteSameStrictSignOrdering_of_card_ge_three_total

/--
info: 'RatFuncWittLocalGlobal.diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_same_universe_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RatFuncWittLocalGlobal.diagonal_isotropic_iff_forall_realClosedExtension_of_card_ge_three_same_universe_total

/--
info: 'RatFuncWittLocalGlobal.quadraticForm_not_anisotropic_iff_forall_realClosedExtension_same_universe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RatFuncWittLocalGlobal.quadraticForm_not_anisotropic_iff_forall_realClosedExtension_same_universe
