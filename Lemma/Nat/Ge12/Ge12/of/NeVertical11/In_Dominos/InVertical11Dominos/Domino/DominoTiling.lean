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
  (T : DominoTiling (n + 1) 2)
  (hv : vertical_1_1 ∈ T.dominos)
  (d : Domino)
  (hd : d ∈ T.dominos)
  (hne : d ≠ vertical_1_1) :
-- imply
  d.cell1.1 ≥ 2 ∧ d.cell2.1 ≥ 2 := by
-- proof
  have hdisj := T.pairwise_disjoint d hd vertical_1_1 hv hne
  rw [Finset.disjoint_iff_ne] at hdisj
  have hcols := domino_cells_col_ge_one T d hd
  constructor
  ·
    by_contra h
    push Not at h
    have h1 : d.cell1.1 = 1 := by omega
    have hd_in := T.dominos_in_rect d hd
    have hc1_in_d : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
    have hc1_in_rect := hd_in hc1_in_d
    rw [mem_Rectangle] at hc1_in_rect
    have hrow_bound : d.cell1.2 = 1 ∨ d.cell1.2 = 2 := by omega
    obtain hr1 | hr2 := hrow_bound
    ·
      have heq : d.cell1 = (1, 1) := Prod.ext h1 hr1
      have hv_c1 : vertical_1_1.cell1 ∈ vertical_1_1.cells := Finset.mem_insert_self _ _
      exact hdisj d.cell1 hc1_in_d vertical_1_1.cell1 hv_c1 (by simp [heq])
    ·
      have heq : d.cell1 = (1, 2) := Prod.ext h1 hr2
      have hv_c2 : vertical_1_1.cell2 ∈ vertical_1_1.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact hdisj d.cell1 hc1_in_d vertical_1_1.cell2 hv_c2 (by simp [heq])
  ·
    by_contra h
    push Not at h
    have h2 : d.cell2.1 = 1 := by omega
    have hd_in := T.dominos_in_rect d hd
    have hc2_in_d : d.cell2 ∈ d.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hc2_in_rect := hd_in hc2_in_d
    rw [mem_Rectangle] at hc2_in_rect
    have hrow_bound : d.cell2.2 = 1 ∨ d.cell2.2 = 2 := by omega
    obtain hr1 | hr2 := hrow_bound
    ·
      have heq : d.cell2 = (1, 1) := Prod.ext h2 hr1
      have hv_c1 : vertical_1_1.cell1 ∈ vertical_1_1.cells := Finset.mem_insert_self _ _
      exact hdisj d.cell2 hc2_in_d vertical_1_1.cell1 hv_c1 (by simp [heq])
    ·
      have heq : d.cell2 = (1, 2) := Prod.ext h2 hr2
      have hv_c2 : vertical_1_1.cell2 ∈ vertical_1_1.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact hdisj d.cell2 hc2_in_d vertical_1_1.cell2 hv_c2 (by simp [heq])


-- created on 2026-10-20
