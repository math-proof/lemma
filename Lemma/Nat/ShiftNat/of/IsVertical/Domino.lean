import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings
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
  (h : d.isVertical)
  (k : ℕ) :
-- imply
  (d.shiftNat k).isVertical := by
-- proof
  simp only [isVertical, Cell1Eq1Add.of.Domino, Cell2Eq1Add.of.Domino] at h ⊢
  omega


-- created on 2026-10-20
