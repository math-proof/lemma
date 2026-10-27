import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part9
open Finset BigOperators


namespace DominoTilings

namespace DominoTiling

variable {n m : ℕ}


theorem other_dominos_col_ge_3_gen (T : DominoTiling (n + 2) 2) (d1 d2 : Domino)
    (hd1 : d1 ∈ T.dominos) (hd2 : d2 ∈ T.dominos)
    (hd1_cells : d1.cells = ({(1, 1), (2, 1)} : Finset Cell))
    (hd2_cells : d2.cells = ({(1, 2), (2, 2)} : Finset Cell))
    (d : Domino) (hd : d ∈ T.dominos) (hne1 : d ≠ d1) (hne2 : d ≠ d2) :
    d.cell1.1 ≥ 3 ∧ d.cell2.1 ≥ 3 := by
  have hdisj1 := T.pairwise_disjoint d hd d1 hd1 hne1
  have hdisj2 := T.pairwise_disjoint d hd d2 hd2 hne2
  rw [Finset.disjoint_iff_ne] at hdisj1 hdisj2
  have hcols := domino_cells_col_ge_one T d hd
  -- d1 covers (1,1) and (2,1), d2 covers (1,2) and (2,2)
  have h11 : (1, 1) ∈ d1.cells := by rw [hd1_cells]; simp
  have h21 : (2, 1) ∈ d1.cells := by rw [hd1_cells]; simp
  have h12 : (1, 2) ∈ d2.cells := by rw [hd2_cells]; simp
  have h22 : (2, 2) ∈ d2.cells := by rw [hd2_cells]; simp
  have hd_in := T.dominos_in_rect d hd
  constructor
  · by_contra h
    push Not at h
    have hc1_col : d.cell1.1 = 1 ∨ d.cell1.1 = 2 := by omega
    have hc1_in_d : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
    have hc1_in_rect := hd_in hc1_in_d
    rw [mem_Rectangle] at hc1_in_rect
    have hrow_bound : d.cell1.2 = 1 ∨ d.cell1.2 = 2 := by omega
    rcases hc1_col with hcol1 | hcol2 <;> rcases hrow_bound with hr1 | hr2
    · have heq : d.cell1 = (1, 1) := Prod.ext hcol1 hr1
      exact hdisj1 d.cell1 hc1_in_d (1, 1) h11 heq
    · have heq : d.cell1 = (1, 2) := Prod.ext hcol1 hr2
      exact hdisj2 d.cell1 hc1_in_d (1, 2) h12 heq
    · have heq : d.cell1 = (2, 1) := Prod.ext hcol2 hr1
      exact hdisj1 d.cell1 hc1_in_d (2, 1) h21 heq
    · have heq : d.cell1 = (2, 2) := Prod.ext hcol2 hr2
      exact hdisj2 d.cell1 hc1_in_d (2, 2) h22 heq
  · by_contra h
    push Not at h
    have hc2_col : d.cell2.1 = 1 ∨ d.cell2.1 = 2 := by omega
    have hc2_in_d : d.cell2 ∈ d.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hc2_in_rect := hd_in hc2_in_d
    rw [mem_Rectangle] at hc2_in_rect
    have hrow_bound : d.cell2.2 = 1 ∨ d.cell2.2 = 2 := by omega
    rcases hc2_col with hcol1 | hcol2 <;> rcases hrow_bound with hr1 | hr2
    · have heq : d.cell2 = (1, 1) := Prod.ext hcol1 hr1
      exact hdisj1 d.cell2 hc2_in_d (1, 1) h11 heq
    · have heq : d.cell2 = (1, 2) := Prod.ext hcol1 hr2
      exact hdisj2 d.cell2 hc2_in_d (1, 2) h12 heq
    · have heq : d.cell2 = (2, 1) := Prod.ext hcol2 hr1
      exact hdisj1 d.cell2 hc2_in_d (2, 1) h21 heq
    · have heq : d.cell2 = (2, 2) := Prod.ext hcol2 hr2
      exact hdisj2 d.cell2 hc2_in_d (2, 2) h22 heq


end DominoTiling
end DominoTilings
