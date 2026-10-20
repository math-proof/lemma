import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset
set_option linter.unusedSimpArgs false


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (d : Domino)
  (h : d.cells = vertical_1_1.cells) :
-- imply
  d = vertical_1_1 ∨ d = vertical_1_1_flip := by
-- proof
  simp only [Domino.cells] at h
  have h1 : d.cell1 ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
    have hmem : d.cell1 ∈ ({d.cell1, d.cell2} : Finset Cell) := Finset.mem_insert_self _ _
    rwa [h] at hmem
  have h2 : d.cell2 ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
    have hmem : d.cell2 ∈ ({d.cell1, d.cell2} : Finset Cell) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rwa [h] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  obtain hc1_11 | hc1_12 := h1 <;> obtain hc2_11 | hc2_12 := h2
  ·
    have : d.cell1 = d.cell2 := by simp only [hc1_11, hc2_11]
    exact absurd this d.distinct
  ·
    left
    ext <;> simp only [vertical_1_1, hc1_11, hc2_12]
  ·
    right
    ext <;> simp only [vertical_1_1_flip, hc1_12, hc2_11]
  ·
    have : d.cell1 = d.cell2 := by simp only [hc1_12, hc2_12]
    exact absurd this d.distinct


-- created on 2026-10-20
