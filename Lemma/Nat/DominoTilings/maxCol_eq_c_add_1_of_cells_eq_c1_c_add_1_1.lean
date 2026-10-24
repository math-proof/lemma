import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings
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
  (c : ℕ)
  (d : Domino)
  (h : d.cells = {(c, 1), (c + 1, 1)}) :
-- imply
  d.maxCol = c + 1 := by
-- proof
  simp only [Domino.cells] at h
  have h1 : d.cell1 ∈ ({(c, 1), (c + 1, 1)} : Finset Cell) := by rw [← h]; simp
  have h2 : d.cell2 ∈ ({(c, 1), (c + 1, 1)} : Finset Cell) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  simp only [Domino.maxCol]
  obtain hc1 | hc1 := h1 <;> obtain hc2 | hc2 := h2
  ·
    exfalso
    exact d.distinct (hc1.trans hc2.symm)
  ·
    simp [hc1, hc2]
  ·
    simp [hc1, hc2]
  ·
    exfalso
    exact d.distinct (hc1.trans hc2.symm)


-- created on 2026-10-20
