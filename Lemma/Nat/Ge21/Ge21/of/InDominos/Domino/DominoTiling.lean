import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


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
  d.cell1.2 ≥ 1 ∧ d.cell2.2 ≥ 1 := by
-- proof
  have h := T.dominos_in_rect d hd
  have hc1 : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
  have hc2 : d.cell2 ∈ d.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h1 := h hc1
  have h2 := h hc2
  rw [mem_Rectangle] at h1 h2
  exact ⟨h1.2.2.1, h2.2.2.1⟩


-- created on 2026-10-20
