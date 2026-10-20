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
  (T : DominoTiling (n + 2) 2)
  (d : Domino)
  (hd : d ∈ T.dominos)
  (hcells : d.cells = {(1, 1), (2, 1)}) :
-- imply
  ∃ d' ∈ T.dominos, d' ≠ d ∧ (1, 2) ∈ d'.cells := by
-- proof
  have h12 : (1, 2) ∈ Rectangle (n + 2) 2 := by rw [mem_Rectangle]; omega
  rw [← T.covers_all] at h12
  simp only [Finset.mem_biUnion] at h12
  obtain ⟨d', hd'_mem, hd'_cov⟩ := h12
  use d'
  refine ⟨hd'_mem, ?_, hd'_cov⟩
  intro heq
  subst heq
  rw [hcells] at hd'_cov
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd'_cov
  obtain ⟨_, h⟩ | ⟨_, h⟩ := hd'_cov <;> omega


-- created on 2026-10-20
