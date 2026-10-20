import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (T : DominoTiling (n + 2) 2) :
-- imply
  ∃ x, TilingEquiv (tiling_2_from_sum x) T :=
-- proof
  ⟨tiling_2_to_sum T, tiling_2_roundtrip_TilingEquiv T⟩

end DominoTiling


-- created on 2026-10-20
