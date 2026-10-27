import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (d : Domino) :
-- imply
  d.isHorizontal ∨ d.isVertical := by
-- proof
  obtain ⟨hcol, _⟩ | ⟨hrow, _⟩ := d.adjacent
  · exact Or.inr hcol
  · exact Or.inl hrow


-- created on 2026-10-20
