import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings
import Lemma.Nat.EqVertical11OrEqVertical11Flip.of.Cells.Domino
import Lemma.Nat.Vertical11Flip.of.InVertical11Dominos.DominoTiling
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
  (hv_mem : vertical_1_1 ∈ T.dominos)
  (hv : hasVerticalFirstColumn T) :
-- imply
  Classical.choose hv = vertical_1_1 := by
-- proof
  have hspec := Classical.choose_spec hv -- The chosen domino has cells = vertical_1_1.cells, so it's either vertical_1_1 or vertical_1_1_flip
  obtain heq | heq := EqVertical11OrEqVertical11Flip.of.Cells.Domino _ hspec.2
  · exact heq
  ·
    -- If it were vertical_1_1_flip, then vertical_1_1_flip ∈ T.dominos
    -- But vertical_1_1 ∈ T.dominos, so by disjointness, vertical_1_1_flip ∉ T.dominos
    exfalso
    rw [heq] at hspec
    exact Vertical11Flip.of.InVertical11Dominos.DominoTiling T hv_mem hspec.1


-- created on 2026-10-20
