import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.Cell1Eq1Add.of.Domino
import Lemma.Nat.Cell2Eq1Add.of.Domino
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
  (d : Domino)
  (hc1 : d.cell1.1 ≥ 1)
  (hc2 : d.cell2.1 ≥ 1)
  (k : ℕ) :
-- imply
  (d.shiftNat k).minCol ≥ k + 1 := by
-- proof
  simp only [minCol, Cell1Eq1Add.of.Domino, Cell2Eq1Add.of.Domino, ge_iff_le, le_min_iff]
  omega


-- created on 2026-10-20
