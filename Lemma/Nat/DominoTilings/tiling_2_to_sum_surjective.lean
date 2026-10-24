import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings
import Lemma.Nat.DominoTilings.tiling_2_to_sum_from_sum
open DominoTilings
open Domino DominoTiling
open Finset
open Nat


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main :
-- imply
  Function.Surjective (@tiling_2_to_sum n) :=
-- proof
  fun x =>
  ⟨tiling_2_from_sum x, _root_.Nat.DominoTilings.tiling_2_to_sum_from_sum x⟩


-- created on 2026-10-20
