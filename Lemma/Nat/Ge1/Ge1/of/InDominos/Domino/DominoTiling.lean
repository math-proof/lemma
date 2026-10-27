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
  (T : DominoTiling n m)
  (d : Domino)
  (hd : d ∈ T.dominos) :
-- imply
  d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1 := by
-- proof
  have h := T.dominos_in_rect d hd
  have hc1 : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
  have hc2 : d.cell2 ∈ d.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h1 := h hc1
  have h2 := h hc2
  rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at h1 h2
  exact ⟨h1.1, h2.1⟩


-- created on 2026-10-20
