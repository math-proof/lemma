import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
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
  d.isHorizontal ↔ ¬d.isVertical := by
-- proof
  constructor
  ·
    intro hH hV
    exact NotIsHorizontalAndIsVertical.of.Domino d ⟨hH, hV⟩
  ·
    intro hNV
    obtain hH | hV := IsHorizontalOrIsVertical.of.Domino d
    · exact hH
    · exact absurd hV hNV


-- created on 2026-10-20
