import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
import Lemma.Nat.DominoTilings.hasVerticalFirstColumn_or_horizontalPair
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
  (hnotvert : ¬hasVerticalFirstColumn T) :
-- imply
  (∃ d₁ ∈ T.dominos, d₁.cells = ({(1, 1), (2, 1)} : Finset Cell)) ∧
      (∃ d₂ ∈ T.dominos, d₂.cells = ({(1, 2), (2, 2)} : Finset Cell)) := by
-- proof
  obtain hvert | hhoriz := DominoTilings.hasVerticalFirstColumn_or_horizontalPair T
  · exact absurd hvert hnotvert
  · exact hhoriz


-- created on 2026-10-20
