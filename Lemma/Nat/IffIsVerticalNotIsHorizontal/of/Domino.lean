import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
import Lemma.Nat.IsHorizontalOrIsVertical.of.Domino
import Lemma.Nat.NotIsHorizontalAndIsVertical.of.Domino
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
  (d : Domino) :
-- imply
  d.isVertical ↔ ¬d.isHorizontal := by
-- proof
  constructor
  ·
    intro hV hH
    exact NotIsHorizontalAndIsVertical.of.Domino d ⟨hH, hV⟩
  ·
    intro hNH
    obtain hH | hV := IsHorizontalOrIsVertical.of.Domino d
    · exact absurd hH hNH
    · exact hV


-- created on 2026-10-20
