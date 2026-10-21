import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.EqVertical11OrEqVertical11Flip.of.Cells.Domino
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
  (T : DominoTiling (n + 2) 2)
  (hvert : hasVerticalFirstColumn T) :
-- imply
  vertical_1_1 ∈ T.dominos ∨ vertical_1_1_flip ∈ T.dominos := by
-- proof
  obtain ⟨d, hd_mem, hd_cells⟩ := hvert
  have hd_eq := EqVertical11OrEqVertical11Flip.of.Cells.Domino d (by rw [hd_cells]; rfl)
  obtain rfl | rfl := hd_eq
  ·
    left
    exact hd_mem
  ·
    right
    exact hd_mem


-- created on 2026-10-20
