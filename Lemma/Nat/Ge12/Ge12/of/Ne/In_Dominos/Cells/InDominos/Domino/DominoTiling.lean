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
  (v : Domino)
  (hv : v ∈ T.dominos)
  (hv_cells : v.cells = vertical_1_1.cells)
  (d : Domino)
  (hd : d ∈ T.dominos)
  (hne : d ≠ v) :
-- imply
  d.cell1.1 ≥ 2 ∧ d.cell2.1 ≥ 2 := by
-- proof
  have hdisj := T.pairwise_disjoint d hd v hv hne
  rw [Finset.disjoint_iff_ne] at hdisj
  have hcols := domino_cells_col_ge_one T d hd
  -- v covers (1,1) and (1,2)
  have hv_11 : (1, 1) ∈ v.cells := by rw [hv_cells]; simp [vertical_1_1_cells]
  have hv_12 : (1, 2) ∈ v.cells := by rw [hv_cells]; simp [vertical_1_1_cells]
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
      exact hdisj d.cell1 hc1_in_d (1, 1) hv_11 heq
    ·
      have heq : d.cell1 = (1, 2) := Prod.ext h1 hr2
      exact hdisj d.cell1 hc1_in_d (1, 2) hv_12 heq
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
      exact hdisj d.cell2 hc2_in_d (1, 1) hv_11 heq
    ·
      have heq : d.cell2 = (1, 2) := Prod.ext h2 hr2
      exact hdisj d.cell2 hc2_in_d (1, 2) hv_12 heq


-- created on 2026-10-20
