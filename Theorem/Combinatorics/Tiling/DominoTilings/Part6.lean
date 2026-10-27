import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part8
open Finset BigOperators


namespace DominoTilings

namespace DominoTiling

variable {n m : ℕ}


theorem exists_domino_covering_11 (T : DominoTiling (n + 1) 2) :
    ∃ d ∈ T.dominos, (1, 1) ∈ d.cells := by
  have h11 : (1, 1) ∈ Rectangle (n + 1) 2 := by
    rw [mem_Rectangle]
    omega
  rw [← T.covers_all] at h11
  simp only [Finset.mem_biUnion] at h11
  exact h11


theorem domino_covering_11_cells (T : DominoTiling (n + 2) 2) (d : Domino) (hd : d ∈ T.dominos)
    (hcov : (1, 1) ∈ d.cells) : d.cells = {(1, 1), (1, 2)} ∨ d.cells = {(1, 1), (2, 1)} := by
  have hd_in := T.dominos_in_rect d hd
  have hc1_in := hd_in (Finset.mem_insert_self _ _)
  have hc2_in := hd_in (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [mem_Rectangle] at hc1_in hc2_in
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hcov
  rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
  · left
    rcases hcov with heq | heq
    · have hc1_1 : d.cell1.1 = 1 := congrArg Prod.fst heq.symm
      have hc1_2 : d.cell1.2 = 1 := congrArg Prod.snd heq.symm
      have hc2_1 : d.cell2.1 = 1 := by omega
      rcases hrow with h | h
      · have hc2_2 : d.cell2.2 = 2 := by omega
        have hc2 : d.cell2 = (1, 2) := Prod.ext hc2_1 hc2_2
        simp only [Domino.cells, heq.symm, hc2]
      · omega
    · have hc2_1 : d.cell2.1 = 1 := congrArg Prod.fst heq.symm
      have hc2_2 : d.cell2.2 = 1 := congrArg Prod.snd heq.symm
      have hc1_1 : d.cell1.1 = 1 := by omega
      rcases hrow with h | h
      · omega
      · have hc1_2 : d.cell1.2 = 2 := by omega
        have hc1 : d.cell1 = (1, 2) := Prod.ext hc1_1 hc1_2
        simp only [Domino.cells, hc1, heq.symm, Finset.pair_comm]
  · right
    rcases hcov with heq | heq
    · have hc1_1 : d.cell1.1 = 1 := congrArg Prod.fst heq.symm
      have hc1_2 : d.cell1.2 = 1 := congrArg Prod.snd heq.symm
      have hc2_2 : d.cell2.2 = 1 := by omega
      rcases hcol with h | h
      · have hc2_1 : d.cell2.1 = 2 := by omega
        have hc2 : d.cell2 = (2, 1) := Prod.ext hc2_1 hc2_2
        simp only [Domino.cells, heq.symm, hc2]
      · omega
    · have hc2_1 : d.cell2.1 = 1 := congrArg Prod.fst heq.symm
      have hc2_2 : d.cell2.2 = 1 := congrArg Prod.snd heq.symm
      have hc1_2 : d.cell1.2 = 1 := by omega
      rcases hcol with h | h
      · omega
      · have hc1_1 : d.cell1.1 = 2 := by omega
        have hc1 : d.cell1 = (2, 1) := Prod.ext hc1_1 hc1_2
        simp only [Domino.cells, hc1, heq.symm, Finset.pair_comm]


theorem exists_domino_covering_12_of_horizontal (T : DominoTiling (n + 2) 2) (d : Domino)
    (hd : d ∈ T.dominos) (hcells : d.cells = {(1, 1), (2, 1)}) :
    ∃ d' ∈ T.dominos, d' ≠ d ∧ (1, 2) ∈ d'.cells := by
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
  rcases hd'_cov with ⟨_, h⟩ | ⟨_, h⟩ <;> omega


theorem domino_covering_12_cells (T : DominoTiling (n + 2) 2) (d d' : Domino)
    (hd : d ∈ T.dominos) (hd' : d' ∈ T.dominos) (hne : d' ≠ d)
    (hd_cells : d.cells = {(1, 1), (2, 1)}) (hd'_cov : (1, 2) ∈ d'.cells) :
    d'.cells = {(1, 2), (2, 2)} := by
  have hdisj := T.pairwise_disjoint d' hd' d hd hne
  have hd'_not_11 : (1, 1) ∉ d'.cells := by
    intro h
    rw [Finset.disjoint_iff_ne] at hdisj
    have h11_in_d : (1, 1) ∈ d.cells := by rw [hd_cells]; simp
    exact hdisj (1, 1) h (1, 1) h11_in_d rfl
  have hd'_not_21 : (2, 1) ∉ d'.cells := by
    intro h
    rw [Finset.disjoint_iff_ne] at hdisj
    have h21_in_d : (2, 1) ∈ d.cells := by rw [hd_cells]; simp
    exact hdisj (2, 1) h (2, 1) h21_in_d rfl
  have hd'_in := T.dominos_in_rect d' hd'
  have hc1_in := hd'_in (Finset.mem_insert_self _ _)
  have hc2_in := hd'_in (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [mem_Rectangle] at hc1_in hc2_in
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd'_cov
  rcases d'.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
  · -- d' is vertical
    rcases hd'_cov with heq | heq
    · have hc1_1 : d'.cell1.1 = 1 := congrArg Prod.fst heq.symm
      have hc1_2 : d'.cell1.2 = 2 := congrArg Prod.snd heq.symm
      have hc2_1 : d'.cell2.1 = 1 := by omega
      rcases hrow with h | h
      · omega
      · have hc2_2 : d'.cell2.2 = 1 := by omega
        have hc2 : d'.cell2 = (1, 1) := Prod.ext hc2_1 hc2_2
        have h11_in_d' : (1, 1) ∈ d'.cells := by
          simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
          right; exact hc2.symm
        exact absurd h11_in_d' hd'_not_11
    · have hc2_1 : d'.cell2.1 = 1 := congrArg Prod.fst heq.symm
      have hc2_2 : d'.cell2.2 = 2 := congrArg Prod.snd heq.symm
      have hc1_1 : d'.cell1.1 = 1 := by omega
      rcases hrow with h | h
      · have hc1_2' : d'.cell1.2 = 1 := by omega
        have hc1 : d'.cell1 = (1, 1) := Prod.ext hc1_1 hc1_2'
        have h11_in_d' : (1, 1) ∈ d'.cells := by
          simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
          left; exact hc1.symm
        exact absurd h11_in_d' hd'_not_11
      · omega
  · -- d' is horizontal
    rcases hd'_cov with heq | heq
    · have hc1_1 : d'.cell1.1 = 1 := congrArg Prod.fst heq.symm
      have hc1_2 : d'.cell1.2 = 2 := congrArg Prod.snd heq.symm
      have hc2_2 : d'.cell2.2 = 2 := by omega
      rcases hcol with h | h
      · have hc2_1 : d'.cell2.1 = 2 := by omega
        have hc2 : d'.cell2 = (2, 2) := Prod.ext hc2_1 hc2_2
        simp only [Domino.cells, heq.symm, hc2]
      · omega
    · have hc2_1 : d'.cell2.1 = 1 := congrArg Prod.fst heq.symm
      have hc2_2 : d'.cell2.2 = 2 := congrArg Prod.snd heq.symm
      have hc1_2 : d'.cell1.2 = 2 := by omega
      rcases hcol with h | h
      · omega
      · have hc1_1 : d'.cell1.1 = 2 := by omega
        have hc1 : d'.cell1 = (2, 2) := Prod.ext hc1_1 hc1_2
        simp only [Domino.cells, hc1, heq.symm, Finset.pair_comm]


end DominoTiling
end DominoTilings
