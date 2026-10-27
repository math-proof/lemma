import Mathlib
import Structure.Combinatorics.Tiling.DominoTilings.Part2
open Finset BigOperators


namespace DominoTilings

namespace DominoTiling

variable {n m : ℕ}


theorem domino_cells_col_ge_one (T : DominoTiling n m) (d : Domino) (hd : d ∈ T.dominos) :
    d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1 := by
  have h := T.dominos_in_rect d hd
  have hc1 : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
  have hc2 : d.cell2 ∈ d.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h1 := h hc1
  have h2 := h hc2
  rw [mem_Rectangle] at h1 h2
  exact ⟨h1.1, h2.1⟩


theorem other_dominos_col_ge_3 (T : DominoTiling (n + 2) 2)
    (hh1 : horizontal_1_1 ∈ T.dominos) (hh2 : horizontal_1_2 ∈ T.dominos)
    (d : Domino) (hd : d ∈ T.dominos) (hne1 : d ≠ horizontal_1_1) (hne2 : d ≠ horizontal_1_2) :
    d.cell1.1 ≥ 3 ∧ d.cell2.1 ≥ 3 := by
  have hdisj1 := T.pairwise_disjoint d hd horizontal_1_1 hh1 hne1
  have hdisj2 := T.pairwise_disjoint d hd horizontal_1_2 hh2 hne2
  have h := domino_cells_col_ge_one T d hd
  constructor
  · by_contra hlt
    push Not at hlt
    have hd_in_rect := T.dominos_in_rect d hd
    have hc1_in_rect := hd_in_rect (Finset.mem_insert_self _ _)
    rw [mem_Rectangle] at hc1_in_rect
    have hrow : d.cell1.2 = 1 ∨ d.cell1.2 = 2 := by omega
    rcases hrow with hr1 | hr2
    · have : d.cell1 ∈ horizontal_1_1.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        have hcol : d.cell1.1 = 1 ∨ d.cell1.1 = 2 := by omega
        rcases hcol with hc1 | hc2
        · left; ext <;> simp [hc1, hr1]
        · right; ext <;> simp [hc2, hr1]
      exact Finset.disjoint_left.mp hdisj1 (Finset.mem_insert_self _ _) this
    · have : d.cell1 ∈ horizontal_1_2.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        have hcol : d.cell1.1 = 1 ∨ d.cell1.1 = 2 := by omega
        rcases hcol with hc1 | hc2
        · left; ext <;> simp [hc1, hr2]
        · right; ext <;> simp [hc2, hr2]
      exact Finset.disjoint_left.mp hdisj2 (Finset.mem_insert_self _ _) this
  · by_contra hlt
    push Not at hlt
    have hd_in_rect := T.dominos_in_rect d hd
    have hc2_in_rect := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [mem_Rectangle] at hc2_in_rect
    have hrow : d.cell2.2 = 1 ∨ d.cell2.2 = 2 := by omega
    rcases hrow with hr1 | hr2
    · have : d.cell2 ∈ horizontal_1_1.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        have hcol : d.cell2.1 = 1 ∨ d.cell2.1 = 2 := by omega
        rcases hcol with hc1 | hc2
        · left; ext <;> simp [hc1, hr1]
        · right; ext <;> simp [hc2, hr1]
      exact Finset.disjoint_left.mp hdisj1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) this
    · have : d.cell2 ∈ horizontal_1_2.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        have hcol : d.cell2.1 = 1 ∨ d.cell2.1 = 2 := by omega
        rcases hcol with hc1 | hc2
        · left; ext <;> simp [hc1, hr2]
        · right; ext <;> simp [hc2, hr2]
      exact Finset.disjoint_left.mp hdisj2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) this


end DominoTiling
end DominoTilings
