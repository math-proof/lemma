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
  (hc1 : d.cell1.1 ≥ 1)
  (hc2 : d.cell2.1 ≥ 1) :
-- imply
  (d.shiftNat k).shiftNeg k (by simp [shiftNat]; omega) (by simp [shiftNat]; omega) = d := by
-- proof
  simp only [shiftNat, shiftNeg]
  ext <;> simp


-- created on 2026-10-20
