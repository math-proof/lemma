import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
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
  Xor d.isHorizontal d.isVertical := by
-- proof
  obtain hH | hV := IsHorizontalOrIsVertical.of.Domino d
  · exact Or.inl ⟨hH, fun hV => NotIsHorizontalAndIsVertical.of.Domino d ⟨hH, hV⟩⟩
  · exact Or.inr ⟨hV, fun hH => NotIsHorizontalAndIsVertical.of.Domino d ⟨hH, hV⟩⟩


-- created on 2026-10-20
