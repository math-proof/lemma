import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
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
  (h : d.isHorizontal)
  (k : ℕ) :
-- imply
  (d.shiftNat k).isHorizontal := by
-- proof
  simp only [isHorizontal, Cell1Eq1Add.of.Domino, Cell2Eq1Add.of.Domino] at h ⊢
  exact h


-- created on 2026-10-20
