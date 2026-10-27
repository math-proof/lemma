import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
import Lemma.Nat.IffIn_RectangleGe1AndGe_1AndGe21AndGe_2
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
  (T : DominoTiling (n + 1) 2) :
-- imply
  ∃ d ∈ T.dominos, (1, 1) ∈ d.cells := by
-- proof
  have h11 : (1, 1) ∈ Rectangle (n + 1) 2 := by
    rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2]
    omega
  rw [← T.covers_all] at h11
  simp only [Finset.mem_biUnion] at h11
  exact h11


-- created on 2026-10-20
