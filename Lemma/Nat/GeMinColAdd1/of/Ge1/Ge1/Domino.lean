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
  (hc1 : d.cell1.1 ≥ 1)
  (hc2 : d.cell2.1 ≥ 1)
  (k : ℕ) :
-- imply
  (d.shiftNat k).minCol ≥ k + 1 := by
-- proof
  simp only [minCol, shiftNat_cell1, shiftNat_cell2, ge_iff_le, le_min_iff]
  omega


-- created on 2026-10-20
