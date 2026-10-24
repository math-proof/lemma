import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (T : DominoTiling (n + 1) 2)
  (hv : vertical_1_1 ∈ T.dominos) :
-- imply
  restrictAfterVerticalGen T vertical_1_1 hv rfl = restrictAfterVertical T hv := by
-- proof
  -- The two functions produce the same result because they use the same
  -- erase and shift operations, just with different proof terms
  rfl


-- created on 2026-10-20
