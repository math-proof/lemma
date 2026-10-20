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
  (d : Domino)
  (k : ℕ)
  (h : d.isHorizontal) :
-- imply
  (d.shiftNat k).isHorizontal := by
-- proof
  simp only [isHorizontal, shiftNat_cell1, shiftNat_cell2] at h ⊢
  exact h


-- created on 2026-10-20
