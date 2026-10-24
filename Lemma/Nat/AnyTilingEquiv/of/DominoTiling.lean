import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings
import Lemma.Nat.DominoTilings.tiling_2_roundtrip_TilingEquiv
open DominoTilings
open Domino DominoTiling
open Finset
open Nat


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
  ⟨tiling_2_to_sum T, _root_.Nat.DominoTilings.tiling_2_roundtrip_TilingEquiv T⟩


-- created on 2026-10-20
