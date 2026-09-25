/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import RatFuncWittLocalGlobal.Ternary.Legendre.ClearedBinary.IsotropyBridge

/-!
# Cleared-binary endpoint
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

theorem clearedBinaryOrSquareRight_of_isSquare_neg_left
    {R : Type u} [Field R] {B C : Polynomial R}
    (hB : IsSquare (-(algebraMap (Polynomial R) (RatFunc R) B))) :
    ClearedBinaryOrSquareRight R B C :=
  (clearedBinaryOrSquareRight_iff_ternary_isotropic B C).mpr
    (Diagonal.ternary_isotropic_one_of_isSquare_neg_left hB)

theorem clearedBinaryRight_of_isSquare_neg_left
    {R : Type u} [Field R] {B C : Polynomial R}
    (hB : IsSquare (-(algebraMap (Polynomial R) (RatFunc R) B)))
    (hC : ¬ IsSquare (-(algebraMap (Polynomial R) (RatFunc R) C))) :
    ClearedBinaryRight R B C := by
  rcases (clearedBinaryOrSquareRight_iff_binary_or_square B C).mp
      (clearedBinaryOrSquareRight_of_isSquare_neg_left hB) with hbinary | hsquare
  · exact hbinary
  · exact False.elim (hC hsquare)

theorem squarefreeBinaryConstructionRightNoObstruction_iff_nonterminal
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    SquarefreeBinaryConstructionRightNoObstruction.{u, v} R ↔
      SquarefreeNonterminalBinaryConstructionRightNoObstruction.{u, v} R := by
  constructor
  · intro h B C hB hC hBsq hCsq hno _ hnotC
    exact h B C hB hC hBsq hCsq hno hnotC
  · intro h B C hB hC hBsq hCsq hno hnotC
    by_cases hsqB : IsSquare (-(algebraMap (Polynomial R) (RatFunc R) B))
    · exact clearedBinaryRight_of_isSquare_neg_left hsqB hnotC
    · exact h B C hB hC hBsq hCsq hno hsqB hnotC

theorem squarefreeNonterminalBinaryConstructionRightNoObstruction_of_noOrdering
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hreal : NormalizedOrderingRealization.{u, v} R)
    (h :
      SquarefreeNonterminalBinaryConstructionRightNoOrderingObstruction R) :
    SquarefreeNonterminalBinaryConstructionRightNoObstruction.{u, v} R := by
  intro B C hB hC hBsq hCsq hno hBterm hCterm
  exact h B C hB hC hBsq hCsq
    (by
      intro hord
      exact hno (hreal _ _ hord))
    hBterm hCterm

end RatFunc
end RatFuncWittLocalGlobal
