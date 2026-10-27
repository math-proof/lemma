import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
import Lemma.Nat.CellsEq1.of.In1Cells.CellsEq1.Ne.InDominos.InDominos.Domino.DominoTiling
import Lemma.Nat.CellsEq1OrCellsEq1.of.In1Cells.InDominos.Domino.DominoTiling
import Lemma.Nat.In1Cells.of.DominoTiling
import Lemma.Nat.NeAnd1InCells.of.CellsEq1.InDominos.Domino.DominoTiling
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
  hasVerticalFirstColumn T ∨
      (∃ d₁ ∈ T.dominos, d₁.cells = ({(1, 1), (2, 1)} : Finset Cell)) ∧
      (∃ d₂ ∈ T.dominos, d₂.cells = ({(1, 2), (2, 2)} : Finset Cell)) := by
-- proof
  obtain ⟨d, hd_mem, hd_cov⟩ := In1Cells.of.DominoTiling T
  obtain hvert | hhoriz := CellsEq1OrCellsEq1.of.In1Cells.InDominos.Domino.DominoTiling T d hd_mem hd_cov
  ·
    left
    exact ⟨d, hd_mem, hvert⟩
  ·
    right
    constructor
    · exact ⟨d, hd_mem, hhoriz⟩
    ·
      obtain ⟨d', hd'_mem, hd'_ne, hd'_cov⟩ := NeAnd1InCells.of.CellsEq1.InDominos.Domino.DominoTiling T d hd_mem hhoriz
      exact ⟨d', hd'_mem, CellsEq1.of.In1Cells.CellsEq1.Ne.InDominos.InDominos.Domino.DominoTiling T d d' hd_mem hd'_mem hd'_ne hhoriz hd'_cov⟩


-- created on 2026-10-20
