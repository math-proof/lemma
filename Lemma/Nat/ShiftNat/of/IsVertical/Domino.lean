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
  (h : d.isVertical)
  (k : ℕ) :
-- imply
  (d.shiftNat k).isVertical := by
-- proof
  simp only [isVertical, shiftNat_cell1, shiftNat_cell2] at h ⊢
  omega


-- created on 2026-10-20
