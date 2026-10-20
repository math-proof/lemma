import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


-- Private helpers (ported from sympy DominoTilings; file-local)

private lemma domino_at_22_options (n : ℕ) (d : Domino)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (2, 2) ∈ d.cells)
    (h_not_12 : (1, 2) ∉ d.cells) :
    d.cells = {(2, 2), (3, 2)} ∨ d.cells = {(2, 1), (2, 2)} ∨ d.cells = {(2, 2), (2, 3)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov h_not_12 ⊢
  have hd_c1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  have hd_c2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  rw [mem_Rectangle] at hd_c1_in hd_c2_in
  rcases h_cov with hc1 | hc2
  · have hc1_eq : d.cell1 = (2, 2) := hc1.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · have hc2_col : d.cell2.1 = 2 := by rw [← hcol, hc1_eq]
      rcases hrow with h | h
      · have hc2_eq : d.cell2 = (2, 3) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; right; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (2, 1) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc2_row : d.cell2.2 = 2 := by rw [← hrow, hc1_eq]
      rcases hcol with h | h
      · have hc2_eq : d.cell2 = (3, 2) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        left; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (1, 2) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        exfalso; apply h_not_12; right; exact hc2_eq.symm
  · have hc2_eq : d.cell2 = (2, 2) := hc2.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · have hc1_col : d.cell1.1 = 2 := by rw [hcol, hc2_eq]
      rcases hrow with h | h
      · have hc1_eq : d.cell1 = (2, 1) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; left; simp only [hc1_eq, hc2_eq]
      · have hc1_eq : d.cell1 = (2, 3) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; right; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc1_row : d.cell1.2 = 2 := by rw [hrow, hc2_eq]
      rcases hcol with h | h
      · have hc1_eq : d.cell1 = (1, 2) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        exfalso; apply h_not_12; left; exact hc1_eq.symm
      · have hc1_eq : d.cell1 = (3, 2) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]

private lemma domino_at_23_options (n : ℕ) (d : Domino)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (2, 3) ∈ d.cells)
    (h_not_13 : (1, 3) ∉ d.cells) :
    d.cells = {(2, 3), (3, 3)} ∨ d.cells = {(2, 2), (2, 3)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov h_not_13 ⊢
  have hd_c1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  have hd_c2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  rw [mem_Rectangle] at hd_c1_in hd_c2_in
  rcases h_cov with hc1 | hc2
  · have hc1_eq : d.cell1 = (2, 3) := hc1.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · have hc2_col : d.cell2.1 = 2 := by rw [← hcol, hc1_eq]
      rcases hrow with h | h
      · exfalso
        have hc2_row : d.cell2.2 = 4 := by rw [hc1_eq] at h; omega
        omega
      · have hc2_eq : d.cell2 = (2, 2) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc2_row : d.cell2.2 = 3 := by rw [← hrow, hc1_eq]
      rcases hcol with h | h
      · have hc2_eq : d.cell2 = (3, 3) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        left; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (1, 3) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        exfalso; apply h_not_13; right; exact hc2_eq.symm
  · have hc2_eq : d.cell2 = (2, 3) := hc2.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · have hc1_col : d.cell1.1 = 2 := by rw [hcol, hc2_eq]
      rcases hrow with h | h
      · have hc1_eq : d.cell1 = (2, 2) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; simp only [hc1_eq, hc2_eq]
      · exfalso
        have hc1_row : d.cell1.2 = 4 := by rw [hc2_eq] at h; omega
        omega
    · have hc1_row : d.cell1.2 = 3 := by rw [hrow, hc2_eq]
      rcases hcol with h | h
      · have hc1_eq : d.cell1 = (1, 3) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        exfalso; apply h_not_13; left; exact hc1_eq.symm
      · have hc1_eq : d.cell1 = (3, 3) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]

private lemma maxCol_eq_2_of_cells_eq_11_21 (d : Domino) (h : d.cells = {(1, 1), (2, 1)}) :
    d.maxCol = 2 := by
  simp only [Domino.cells] at h
  have h1 : d.cell1 ∈ ({(1, 1), (2, 1)} : Finset Cell) := by rw [← h]; simp
  have h2 : d.cell2 ∈ ({(1, 1), (2, 1)} : Finset Cell) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  simp only [Domino.maxCol]
  rcases h1 with hc1 | hc1 <;> rcases h2 with hc2 | hc2
  · exfalso; exact d.distinct (hc1.trans hc2.symm)
  · simp [hc1, hc2]
  · simp [hc1, hc2]
  · exfalso; exact d.distinct (hc1.trans hc2.symm)

private lemma minCol_maxCol_eq_2_of_cells_eq_22_23 (d : Domino) (h : d.cells = {(2, 2), (2, 3)}) :
    d.minCol = 2 ∧ d.maxCol = 2 := by
  simp only [Domino.cells] at h
  have h1 : d.cell1 ∈ ({(2, 2), (2, 3)} : Finset Cell) := by rw [← h]; simp
  have h2 : d.cell2 ∈ ({(2, 2), (2, 3)} : Finset Cell) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  simp only [Domino.minCol, Domino.maxCol]
  rcases h1 with hc1 | hc1 <;> rcases h2 with hc2 | hc2
  · exfalso; exact d.distinct (hc1.trans hc2.symm)
  · simp [hc1, hc2]
  · simp [hc1, hc2]
  · exfalso; exact d.distinct (hc1.trans hc2.symm)

private lemma domino_at_c1_forced_right (n c : ℕ) (d : Domino)
    (_hc_ge : c ≥ 1) (_hc_lt : c < n)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (c, 1) ∈ d.cells)
    (h_not_left : (c - 1, 1) ∉ d.cells) (h_not_up : (c, 2) ∉ d.cells) :
    d.cells = {(c, 1), (c + 1, 1)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov h_not_left h_not_up
  have hd_c1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  have hd_c2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  rw [mem_Rectangle] at hd_c1_in hd_c2_in
  rcases h_cov with hc1 | hc2
  · -- (c, 1) = d.cell1
    have hc1_eq : d.cell1 = (c, 1) := hc1.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · -- vertical domino: columns equal
      have hc2_col : d.cell2.1 = c := by rw [← hcol, hc1_eq]
      rcases hrow with h | h
      · -- d.cell1.2 + 1 = d.cell2.2, so d.cell2 = (c, 2)
        have hc2_eq : d.cell2 = (c, 2) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        exfalso; apply h_not_up; right; exact hc2_eq.symm
      · -- d.cell2.2 + 1 = d.cell1.2, so d.cell2 = (c, 0)
        have hc2_row : d.cell2.2 = 0 := by rw [hc1_eq] at h; omega
        omega -- contradicts hd_c2_in.2.2.1 (row ≥ 1)
    · -- horizontal domino: rows equal
      have hc2_row : d.cell2.2 = 1 := by rw [← hrow, hc1_eq]
      rcases hcol with h | h
      · -- d.cell1.1 + 1 = d.cell2.1, so d.cell2 = (c + 1, 1)
        have hc2_eq : d.cell2 = (c + 1, 1) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        simp only [Domino.cells, hc1_eq, hc2_eq]
      · -- d.cell2.1 + 1 = d.cell1.1, so d.cell2 = (c - 1, 1)
        have hc2_eq : d.cell2 = (c - 1, 1) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        exfalso; apply h_not_left; right; exact hc2_eq.symm
  · -- (c, 1) = d.cell2, symmetric case
    have hc2_eq : d.cell2 = (c, 1) := hc2.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · -- vertical domino
      have hc1_col : d.cell1.1 = c := by rw [hcol, hc2_eq]
      rcases hrow with h | h
      · -- d.cell1.2 + 1 = d.cell2.2, so d.cell1 = (c, 0)
        have hc1_row : d.cell1.2 = 0 := by rw [hc2_eq] at h; omega
        omega -- contradicts hd_c1_in.2.2.1
      · -- d.cell2.2 + 1 = d.cell1.2, so d.cell1 = (c, 2)
        have hc1_eq : d.cell1 = (c, 2) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        exfalso; apply h_not_up; left; exact hc1_eq.symm
    · -- horizontal domino
      have hc1_row : d.cell1.2 = 1 := by rw [hrow, hc2_eq]
      rcases hcol with h | h
      · -- d.cell1.1 + 1 = d.cell2.1, so d.cell1 = (c - 1, 1)
        have hc1_eq : d.cell1 = (c - 1, 1) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        exfalso; apply h_not_left; left; exact hc1_eq.symm
      · -- d.cell2.1 + 1 = d.cell1.1, so d.cell1 = (c + 1, 1)
        have hc1_eq : d.cell1 = (c + 1, 1) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        simp only [Domino.cells, hc1_eq, hc2_eq, Finset.pair_comm]

private lemma domino_at_c2_options (n c : ℕ) (d : Domino)
    (_hc_ge : c ≥ 1) (_hc_lt : c < n)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (c, 2) ∈ d.cells)
    (h_not_left : (c - 1, 2) ∉ d.cells) :
    d.cells = {(c, 2), (c + 1, 2)} ∨ d.cells = {(c, 1), (c, 2)} ∨ d.cells = {(c, 2), (c, 3)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov h_not_left ⊢
  have hd_c1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  have hd_c2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  rw [mem_Rectangle] at hd_c1_in hd_c2_in
  rcases h_cov with hc1 | hc2
  · have hc1_eq : d.cell1 = (c, 2) := hc1.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · have hc2_col : d.cell2.1 = c := by rw [← hcol, hc1_eq]
      rcases hrow with h | h
      · have hc2_eq : d.cell2 = (c, 3) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; right; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (c, 1) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc2_row : d.cell2.2 = 2 := by rw [← hrow, hc1_eq]
      rcases hcol with h | h
      · have hc2_eq : d.cell2 = (c + 1, 2) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        left; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (c - 1, 2) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        exfalso; apply h_not_left; right; exact hc2_eq.symm
  · have hc2_eq : d.cell2 = (c, 2) := hc2.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · have hc1_col : d.cell1.1 = c := by rw [hcol, hc2_eq]
      rcases hrow with h | h
      · have hc1_eq : d.cell1 = (c, 1) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; left; simp only [hc1_eq, hc2_eq]
      · have hc1_eq : d.cell1 = (c, 3) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; right; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc1_row : d.cell1.2 = 2 := by rw [hrow, hc2_eq]
      rcases hcol with h | h
      · have hc1_eq : d.cell1 = (c - 1, 2) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        exfalso; apply h_not_left; left; exact hc1_eq.symm
      · have hc1_eq : d.cell1 = (c + 1, 2) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]

private lemma domino_at_c3_options (n c : ℕ) (d : Domino)
    (_hc_ge : c ≥ 1) (_hc_lt : c < n)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (c, 3) ∈ d.cells)
    (h_not_left : (c - 1, 3) ∉ d.cells) :
    d.cells = {(c, 3), (c + 1, 3)} ∨ d.cells = {(c, 2), (c, 3)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov h_not_left ⊢
  have hd_c1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  have hd_c2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  rw [mem_Rectangle] at hd_c1_in hd_c2_in
  rcases h_cov with hc1 | hc2
  · have hc1_eq : d.cell1 = (c, 3) := hc1.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · have hc2_col : d.cell2.1 = c := by rw [← hcol, hc1_eq]
      rcases hrow with h | h
      · exfalso
        have hc2_row : d.cell2.2 = 4 := by rw [hc1_eq] at h; omega
        omega
      · have hc2_eq : d.cell2 = (c, 2) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc2_row : d.cell2.2 = 3 := by rw [← hrow, hc1_eq]
      rcases hcol with h | h
      · have hc2_eq : d.cell2 = (c + 1, 3) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        left; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (c - 1, 3) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        exfalso; apply h_not_left; right; exact hc2_eq.symm
  · have hc2_eq : d.cell2 = (c, 3) := hc2.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · have hc1_col : d.cell1.1 = c := by rw [hcol, hc2_eq]
      rcases hrow with h | h
      · have hc1_eq : d.cell1 = (c, 2) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; simp only [hc1_eq, hc2_eq]
      · exfalso
        have hc1_row : d.cell1.2 = 4 := by rw [hc2_eq] at h; omega
        omega
    · have hc1_row : d.cell1.2 = 3 := by rw [hrow, hc2_eq]
      rcases hcol with h | h
      · have hc1_eq : d.cell1 = (c - 1, 3) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        exfalso; apply h_not_left; left; exact hc1_eq.symm
      · have hc1_eq : d.cell1 = (c + 1, 3) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]

private lemma minCol_maxCol_eq_c_of_cells_eq_c2_c3 (c : ℕ) (d : Domino) (h : d.cells = {(c, 2), (c, 3)}) :
    d.minCol = c ∧ d.maxCol = c := by
  simp only [Domino.cells] at h
  have h1 : d.cell1 ∈ ({(c, 2), (c, 3)} : Finset Cell) := by rw [← h]; simp
  have h2 : d.cell2 ∈ ({(c, 2), (c, 3)} : Finset Cell) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  simp only [Domino.minCol, Domino.maxCol]
  rcases h1 with hc1 | hc1 <;> rcases h2 with hc2 | hc2
  · exfalso; exact d.distinct (hc1.trans hc2.symm)
  · simp [hc1, hc2]
  · simp [hc1, hc2]
  · exfalso; exact d.distinct (hc1.trans hc2.symm)

private lemma maxCol_eq_c_add_1_of_cells_eq_c1_c_add_1_1 (c : ℕ) (d : Domino) (h : d.cells = {(c, 1), (c + 1, 1)}) :
    d.maxCol = c + 1 := by
  simp only [Domino.cells] at h
  have h1 : d.cell1 ∈ ({(c, 1), (c + 1, 1)} : Finset Cell) := by rw [← h]; simp
  have h2 : d.cell2 ∈ ({(c, 1), (c + 1, 1)} : Finset Cell) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  simp only [Domino.maxCol]
  rcases h1 with hc1 | hc1 <;> rcases h2 with hc2 | hc2
  · exfalso; exact d.distinct (hc1.trans hc2.symm)
  · simp [hc1, hc2]
  · simp [hc1, hc2]
  · exfalso; exact d.distinct (hc1.trans hc2.symm)

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree)
  (htop : T.hasTopVerticalInCol 1)
  (i : ℕ)
  (hi_pos : i ≥ 1)
  (hi_lt : i < n / 2) :
-- imply
  -- T contains the basement domino covering cells {(2i-1, 1), (2i, 1)}
      (∃ d ∈ T.dominos, d.cells = {(2*i - 1, 1), (2*i, 1)}) ∧
      -- T contains the middle domino covering cells {(2i, 2), (2i+1, 2)}
      (∃ d ∈ T.dominos, d.cells = {(2*i, 2), (2*i + 1, 2)}) ∧
      -- T contains the top domino covering cells {(2i, 3), (2i+1, 3)}
      (∃ d ∈ T.dominos, d.cells = {(2*i, 3), (2*i + 1, 3)})
  := by
-- proof
  -- The proof is by strong induction on i.
  -- For each i with 1 ≤ i < n/2, we prove:
  -- 1. T contains basement domino: cell1 = (2i-1, 1), cell2 = (2i, 1)
  -- 2. T contains middle domino: cell1 = (2i, 2), cell2 = (2i+1, 2)
  -- 3. T contains top domino: cell1 = (2i, 3), cell2 = (2i+1, 3)
  --
  -- Base case (i=1):
  -- - htop gives us a vertical domino in col 1 covering rows 2-3
  -- - Cell (1,1) must be covered by some domino d
  -- - d can't be vertical (col 1 rows 2-3 already covered)
  -- - d must be horizontal going right: {(1,1), (2,1)}
  -- - This is the basement domino for i=1
  -- - Now (2,2) and (2,3) must be covered
  -- - If by vertical domino in col 2, then col 2 would end at maxCol=2
  -- - But basement also ends at maxCol=2, creating fault at col 2
  -- - So (2,2) and (2,3) are covered by horizontal dominos going right
  -- - These are the middle and top dominos for i=1
  --
  -- Induction step (j → j+1):
  -- - By IH: basement at (2j-1,1)-(2j,1), middle at (2j,2)-(2j+1,2), top at (2j,3)-(2j+1,3)
  -- - Cell (2j+1, 1) must be covered
  -- - Can't be vertical (would collide with middle domino at (2j+1, 2))
  -- - Can't be horizontal going left (would collide with basement at (2j, 1))
  -- - Must be horizontal going right: {(2j+1, 1), (2j+2, 1)} - basement for j+1
  -- - Now (2j+2, 2) and (2j+2, 3) must be covered
  -- - If by vertical in col 2j+2, then fault at col 2j+2 (basement ends there too)
  -- - So horizontal going right: middle and top for j+1
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_or_lt_of_le hi_pos with hi_eq | hi_gt
    · -- Base case: i = 1
      subst hi_eq
      simp only [Nat.mul_one, Nat.reduceSubDiff]
      -- From hi_lt : 1 < n / 2, we get n ≥ 4
      have hn_ge_2 : n ≥ 2 := by omega
      -- Get basement domino from base_case_basement
      obtain ⟨d_base, hd_base_mem, hd_base_cells⟩ := base_case_basement n T htop hn_ge_2
      -- Get the top vertical domino info
      obtain ⟨d_top, hd_top_mem, hd_top_vert, hd_top_col, hd_top_rows⟩ := htop
      -- The top vertical covers (1, 2) and (1, 3)
      have hd_top_c2_col : d_top.cell2.1 = 1 := hd_top_vert.symm.trans hd_top_col
      have hd_top_covers_12 : (1, 2) ∈ d_top.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        obtain ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩ := hd_top_rows
        · left; ext; exact hd_top_col.symm; omega
        · right; ext; exact hd_top_c2_col.symm; omega
      have hd_top_covers_13 : (1, 3) ∈ d_top.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        obtain ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩ := hd_top_rows
        · right; ext; exact hd_top_c2_col.symm; omega
        · left; ext; exact hd_top_col.symm; omega
      -- Cell (2, 2) must be covered by some domino d_mid
      have h22_in : (2, 2) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
      obtain ⟨d_mid, hd_mid_mem, hd_mid_cov⟩ := T.cell_covered (2, 2) h22_in
      -- d_mid doesn't cover (1, 2) (that's covered by d_top)
      have hd_mid_ne_top : d_mid ≠ d_top := by
        intro heq
        subst heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd_mid_cov
        rcases hd_mid_cov with h | h
        · have hcol : d_mid.cell1.1 = 2 := by rw [← h]
          rw [hd_top_col] at hcol
          omega
        · have hcol : d_mid.cell2.1 = 2 := by rw [← h]
          rw [hd_top_c2_col] at hcol
          omega
      have hd_mid_not_12 : (1, 2) ∉ d_mid.cells := by
        intro h12
        have heq := T.cell_covered_unique (1, 2) d_mid d_top hd_mid_mem hd_top_mem h12 hd_top_covers_12
        exact hd_mid_ne_top heq
      -- The middle domino must be horizontal going right: {(2,2), (3,2)}
      -- (vertical would create fault at col 2, horizontal left blocked by top vertical at (1,2))
      have hd_mid_cells : d_mid.cells = {(2, 2), (3, 2)} := by
        have hn_ge_3 : n ≥ 3 := by omega
        have hd_mid_in_rect := T.dominos_in_rect d_mid hd_mid_mem
        have h_opts := domino_at_22_options n d_mid hd_mid_in_rect hd_mid_cov hd_mid_not_12
        rcases h_opts with h_horiz | h_vert_down | h_vert_up
        · exact h_horiz
        · -- Case {(2, 1), (2, 2)}: d_mid covers (2, 1), but d_base also covers (2, 1)
          exfalso
          have h21_in_mid : (2, 1) ∈ d_mid.cells := by rw [h_vert_down]; simp
          have h21_in_base : (2, 1) ∈ d_base.cells := by rw [hd_base_cells]; simp
          have heq := T.cell_covered_unique (2, 1) d_mid d_base hd_mid_mem hd_base_mem h21_in_mid h21_in_base
          rw [heq, hd_base_cells] at h_vert_down
          have : (2, 2) ∈ ({(1, 1), (2, 1)} : Finset Cell) := by rw [h_vert_down]; simp
          simp at this
        · -- Case {(2, 2), (2, 3)}: Creates fault at column 2
          exfalso
          -- Show that no domino in T spans column 2
          have hfault : T.hasFaultAt 2 := by
            constructor
            · omega
            constructor
            · omega
            intro d hd_mem' ⟨hmin, hmax⟩
            -- d spans column 2, so it has a cell in column 2 with maxCol ≥ 3
            -- The cells in column 2 are (2,1), (2,2), (2,3)
            -- (2,1) is covered by d_base with maxCol = 2
            -- (2,2) and (2,3) are covered by d_mid with maxCol = 2
            -- So d must be one of d_base or d_mid, both have maxCol = 2, contradiction
            have hd_maxCol_ge_3 : d.maxCol ≥ 3 := by omega
            -- d has minCol ≤ 2 and maxCol ≥ 3, so d is horizontal spanning columns 2-3
            -- This means d has a cell in column 2
            have hd_col2_cell : ∃ r, (2, r) ∈ d.cells := by
              -- Since minCol ≤ 2 and maxCol ≥ 3, and dominos are adjacent pairs,
              -- the domino must have one cell with column 2 and one with column 3
              have hd_horiz : d.isHorizontal := by
                unfold Domino.isHorizontal
                obtain ⟨hcol, _⟩ | ⟨hrow, _⟩ := d.adjacent
                · -- vertical: minCol = maxCol, but we have minCol ≤ 2 < 3 ≤ maxCol
                  simp only [Domino.minCol, Domino.maxCol] at hmin hmax
                  have : d.cell1.1 = d.cell2.1 := hcol
                  omega
                · exact hrow
              -- d is horizontal with minCol ≤ 2 < maxCol
              simp only [Domino.minCol, Domino.maxCol] at hmin hmax
              -- Since d is horizontal and adjacent, |cell1.1 - cell2.1| = 1
              have hadj : d.cell1.1 + 1 = d.cell2.1 ∨ d.cell2.1 + 1 = d.cell1.1 := by
                obtain ⟨hvert, _⟩ | ⟨_, hcol⟩ := d.adjacent
                · -- vertical case: contradicts that d is horizontal
                  exfalso
                  simp only [Domino.isHorizontal] at hd_horiz
                  -- hvert says columns are equal, but hmin ≤ 2 < hmax means columns differ
                  omega
                · exact hcol
              have hc1_or_c2 : d.cell1.1 = 2 ∨ d.cell2.1 = 2 := by
                rcases hadj with h | h
                · -- d.cell1.1 + 1 = d.cell2.1
                  have ha_le : d.cell1.1 ≤ 2 := by simp only [min_def] at hmin; split_ifs at hmin <;> omega
                  have hb_gt : d.cell2.1 > 2 := by simp only [max_def] at hmax; split_ifs at hmax <;> omega
                  left; omega
                · -- d.cell2.1 + 1 = d.cell1.1
                  have hb_le : d.cell2.1 ≤ 2 := by simp only [min_def] at hmin; split_ifs at hmin <;> omega
                  have ha_gt : d.cell1.1 > 2 := by simp only [max_def] at hmax; split_ifs at hmax <;> omega
                  right; omega
              rcases hc1_or_c2 with hc1 | hc2
              · have heq : (2, d.cell1.2) = d.cell1 := by ext <;> simp [hc1]
                exact ⟨d.cell1.2, by simp [Domino.cells, heq]⟩
              · have heq : (2, d.cell2.2) = d.cell2 := by ext <;> simp [hc2]
                exact ⟨d.cell2.2, by simp [Domino.cells, heq]⟩
            obtain ⟨r, hr_in⟩ := hd_col2_cell
            -- (2, r) is in column 2, so r ∈ {1, 2, 3}
            have hd_in_rect := T.dominos_in_rect d hd_mem'
            have h2r_in_rect : (2, r) ∈ Rectangle n 3 := hd_in_rect hr_in
            rw [mem_Rectangle] at h2r_in_rect
            have hr_range : r = 1 ∨ r = 2 ∨ r = 3 := by omega
            rcases hr_range with hr1 | hr2 | hr3
            · -- (2, 1) is covered by d_base
              subst hr1
              have heq := T.cell_covered_unique (2, 1) d d_base hd_mem' hd_base_mem hr_in
                (by rw [hd_base_cells]; simp)
              rw [heq] at hd_maxCol_ge_3
              have hbase_max : d_base.maxCol = 2 := maxCol_eq_2_of_cells_eq_11_21 d_base hd_base_cells
              omega
            · -- (2, 2) is covered by d_mid
              subst hr2
              have heq := T.cell_covered_unique (2, 2) d d_mid hd_mem' hd_mid_mem hr_in hd_mid_cov
              rw [heq] at hd_maxCol_ge_3
              have hmid_minmax := minCol_maxCol_eq_2_of_cells_eq_22_23 d_mid h_vert_up
              omega
            · -- (2, 3) is covered by d_mid (since d_mid = {(2,2), (2,3)})
              subst hr3
              have h23_in_mid : (2, 3) ∈ d_mid.cells := by rw [h_vert_up]; simp
              have heq := T.cell_covered_unique (2, 3) d d_mid hd_mem' hd_mid_mem hr_in h23_in_mid
              rw [heq] at hd_maxCol_ge_3
              have hmid_minmax := minCol_maxCol_eq_2_of_cells_eq_22_23 d_mid h_vert_up
              omega
          -- But T is faultfree
          exact hfree 2 (by omega) (by omega) hfault
      -- Similarly for top domino covering (2, 3)
      have h23_in : (2, 3) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
      obtain ⟨d_top', hd_top'_mem, hd_top'_cov⟩ := T.cell_covered (2, 3) h23_in
      have hd_top'_ne_top : d_top' ≠ d_top := by
        intro heq
        subst heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd_top'_cov
        rcases hd_top'_cov with h | h
        · have hcol : d_top'.cell1.1 = 2 := by rw [← h]
          rw [hd_top_col] at hcol
          omega
        · have hcol : d_top'.cell2.1 = 2 := by rw [← h]
          rw [hd_top_c2_col] at hcol
          omega
      have hd_top'_not_13 : (1, 3) ∉ d_top'.cells := by
        intro h13
        have heq := T.cell_covered_unique (1, 3) d_top' d_top hd_top'_mem hd_top_mem h13 hd_top_covers_13
        exact hd_top'_ne_top heq
      have hd_top'_cells : d_top'.cells = {(2, 3), (3, 3)} := by
        have hd_top'_in_rect := T.dominos_in_rect d_top' hd_top'_mem
        have h_opts := domino_at_23_options n d_top' hd_top'_in_rect hd_top'_cov hd_top'_not_13
        rcases h_opts with h_horiz | h_vert
        · exact h_horiz
        · -- Case {(2, 2), (2, 3)}: d_top' covers (2, 2), but d_mid also covers (2, 2)
          -- So d_top' = d_mid, but d_mid.cells = {(2, 2), (3, 2)} ≠ {(2, 2), (2, 3)}
          exfalso
          have h22_in_top' : (2, 2) ∈ d_top'.cells := by rw [h_vert]; simp
          have heq := T.cell_covered_unique (2, 2) d_top' d_mid hd_top'_mem hd_mid_mem h22_in_top' hd_mid_cov
          rw [heq, hd_mid_cells] at h_vert
          have : (2, 3) ∈ ({(2, 2), (3, 2)} : Finset Cell) := by rw [h_vert]; simp
          simp at this
      exact ⟨⟨d_base, hd_base_mem, hd_base_cells⟩,
             ⟨d_mid, hd_mid_mem, hd_mid_cells⟩,
             ⟨d_top', hd_top'_mem, hd_top'_cells⟩⟩
    · -- Induction step: i > 1
      have hi_pred_pos : i - 1 ≥ 1 := by omega
      have hi_pred_lt : i - 1 < n / 2 := by omega
      have hi_pred_lt_i : i - 1 < i := by omega
      have ih_result := ih (i - 1) hi_pred_lt_i hi_pred_pos hi_pred_lt
      obtain ⟨⟨d_base_prev, hd_base_prev_mem, hd_base_prev_cells⟩,
              ⟨d_mid_prev, hd_mid_prev_mem, hd_mid_prev_cells⟩,
              ⟨d_top_prev, hd_top_prev_mem, hd_top_prev_cells⟩⟩ := ih_result
      -- The induction step follows the same pattern as the base case
      -- Cell (2i-1, 1) must be covered by a horizontal domino going right
      -- (going left collides with basement from i-1, vertical collides with middle from i-1)
      -- Then (2i, 2) and (2i, 3) must be horizontal going right by faultfreeness

      -- Simplify the IH cells using the fact that i ≥ 2
      have hi_ge_2 : i ≥ 2 := by omega
      have h_sub_add : 2 * i - 2 + 1 = 2 * i - 1 := by omega
      have hprev_base_simp : d_base_prev.cells = {(2*i - 3, 1), (2*i - 2, 1)} := by
        simp only [Nat.mul_sub_one, Nat.sub_sub] at hd_base_prev_cells
        norm_num at hd_base_prev_cells
        exact hd_base_prev_cells
      have hprev_mid_simp : d_mid_prev.cells = {(2*i - 2, 2), (2*i - 1, 2)} := by
        simp only [Nat.mul_sub_one] at hd_mid_prev_cells
        simp only [h_sub_add] at hd_mid_prev_cells
        exact hd_mid_prev_cells
      have hprev_top_simp : d_top_prev.cells = {(2*i - 2, 3), (2*i - 1, 3)} := by
        simp only [Nat.mul_sub_one] at hd_top_prev_cells
        simp only [h_sub_add] at hd_top_prev_cells
        exact hd_top_prev_cells

      -- Cell (2i-1, 1) must be covered by some domino d_base
      have h_cell_base_in : (2*i - 1, 1) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
      obtain ⟨d_base, hd_base_mem, hd_base_cov⟩ := T.cell_covered (2*i - 1, 1) h_cell_base_in

      -- d_base can't cover (2i-2, 1) - that's in d_base_prev
      have hd_base_not_left : (2*i - 2, 1) ∉ d_base.cells := by
        intro h_in_base
        have h_in_prev : (2*i - 2, 1) ∈ d_base_prev.cells := by rw [hprev_base_simp]; simp
        have heq := T.cell_covered_unique (2*i - 2, 1) d_base d_base_prev hd_base_mem hd_base_prev_mem h_in_base h_in_prev
        rw [heq, hprev_base_simp] at hd_base_cov
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_base_cov
        obtain ⟨h1, _⟩ | ⟨h1, _⟩ := hd_base_cov <;> omega

      -- d_base can't cover (2i-1, 2) - that's in d_mid_prev
      have hd_base_not_up : (2*i - 1, 2) ∉ d_base.cells := by
        intro h_in_base
        have h_in_prev : (2*i - 1, 2) ∈ d_mid_prev.cells := by rw [hprev_mid_simp]; simp
        have heq := T.cell_covered_unique (2*i - 1, 2) d_base d_mid_prev hd_base_mem hd_mid_prev_mem h_in_base h_in_prev
        rw [heq, hprev_mid_simp] at hd_base_cov
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_base_cov
        obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hd_base_cov <;> omega

      -- By domino_at_c1_forced_right, d_base must go right
      have hd_base_in_rect := T.dominos_in_rect d_base hd_base_mem
      have hc_ge : 2*i - 1 ≥ 1 := by omega
      have hc_lt : 2*i - 1 < n := by omega
      -- Adjust the cell coordinates for the lemma
      have hd_base_cov' : (2*i - 1, 1) ∈ d_base.cells := hd_base_cov
      have hd_base_not_left' : (2*i - 1 - 1, 1) ∉ d_base.cells := by
        simp only [Nat.sub_sub]; exact hd_base_not_left
      have hd_base_not_up' : (2*i - 1, 2) ∉ d_base.cells := hd_base_not_up
      have hd_base_cells := domino_at_c1_forced_right n (2*i - 1) d_base hc_ge hc_lt 
        hd_base_in_rect hd_base_cov' hd_base_not_left' hd_base_not_up'
      -- Convert back to the form we need
      have hd_base_cells' : d_base.cells = {(2*i - 1, 1), (2*i, 1)} := by
        simp only [Nat.sub_add_cancel (by omega : 2*i ≥ 1)] at hd_base_cells
        exact hd_base_cells

      -- Now for the middle domino covering (2i, 2)
      have h_cell_mid_in : (2*i, 2) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
      obtain ⟨d_mid, hd_mid_mem, hd_mid_cov⟩ := T.cell_covered (2*i, 2) h_cell_mid_in

      -- d_mid can't cover (2i-1, 2) - that's in d_mid_prev
      have hd_mid_not_left : (2*i - 1, 2) ∉ d_mid.cells := by
        intro h_in_mid
        have h_in_prev : (2*i - 1, 2) ∈ d_mid_prev.cells := by rw [hprev_mid_simp]; simp
        have heq := T.cell_covered_unique (2*i - 1, 2) d_mid d_mid_prev hd_mid_mem hd_mid_prev_mem h_in_mid h_in_prev
        rw [heq, hprev_mid_simp] at hd_mid_cov
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_mid_cov
        obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hd_mid_cov <;> omega

      -- Use domino_at_c2_options to classify d_mid
      have hd_mid_in_rect := T.dominos_in_rect d_mid hd_mid_mem
      have hc_mid_ge : 2*i ≥ 1 := by omega
      have hc_mid_lt : 2*i < n := by omega
      have hd_mid_not_left' : (2*i - 1, 2) ∉ d_mid.cells := hd_mid_not_left
      have h_mid_opts := domino_at_c2_options n (2*i) d_mid hc_mid_ge hc_mid_lt 
        hd_mid_in_rect hd_mid_cov hd_mid_not_left'

      have hd_mid_cells : d_mid.cells = {(2*i, 2), (2*i + 1, 2)} := by
        rcases h_mid_opts with h_horiz | h_vert_down | h_vert_up
        · exact h_horiz
        · -- Case {(2i, 1), (2i, 2)}: d_mid covers (2i, 1), but d_base also covers (2i, 1)
          exfalso
          have h_in_mid : (2*i, 1) ∈ d_mid.cells := by rw [h_vert_down]; simp
          have h_in_base : (2*i, 1) ∈ d_base.cells := by rw [hd_base_cells']; simp
          have heq := T.cell_covered_unique (2*i, 1) d_mid d_base hd_mid_mem hd_base_mem h_in_mid h_in_base
          rw [heq, hd_base_cells'] at h_vert_down
          have hmem : (2*i, 2) ∈ ({(2*i - 1, 1), (2*i, 1)} : Finset Cell) := by rw [h_vert_down]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
          obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hmem <;> omega
        · -- Case {(2i, 2), (2i, 3)}: Creates fault at column 2i
          exfalso
          -- Show that no domino in T spans column 2i
          have hfault : T.hasFaultAt (2*i) := by
            constructor
            · omega
            constructor
            · omega
            intro d hd_mem' ⟨hmin, hmax⟩
            have hd_maxCol_ge : d.maxCol ≥ 2*i + 1 := by omega
            -- d has minCol ≤ 2i and maxCol ≥ 2i+1, so d is horizontal spanning columns 2i and 2i+1
            have hd_col_cell : ∃ r, (2*i, r) ∈ d.cells := by
              have hd_horiz : d.isHorizontal := by
                unfold Domino.isHorizontal
                obtain ⟨hcol, _⟩ | ⟨hrow, _⟩ := d.adjacent
                · simp only [Domino.minCol, Domino.maxCol] at hmin hmax
                  have : d.cell1.1 = d.cell2.1 := hcol
                  omega
                · exact hrow
              simp only [Domino.minCol, Domino.maxCol] at hmin hmax
              have hadj : d.cell1.1 + 1 = d.cell2.1 ∨ d.cell2.1 + 1 = d.cell1.1 := by
                obtain ⟨hvert, _⟩ | ⟨_, hcol⟩ := d.adjacent
                · exfalso; simp only [Domino.isHorizontal] at hd_horiz; omega
                · exact hcol
              have hc1_or_c2 : d.cell1.1 = 2*i ∨ d.cell2.1 = 2*i := by
                rcases hadj with h | h
                · have ha_le : d.cell1.1 ≤ 2*i := by simp only [min_def] at hmin; split_ifs at hmin <;> omega
                  have hb_gt : d.cell2.1 > 2*i := by simp only [max_def] at hmax; split_ifs at hmax <;> omega
                  left; omega
                · have hb_le : d.cell2.1 ≤ 2*i := by simp only [min_def] at hmin; split_ifs at hmin <;> omega
                  have ha_gt : d.cell1.1 > 2*i := by simp only [max_def] at hmax; split_ifs at hmax <;> omega
                  right; omega
              rcases hc1_or_c2 with hc1 | hc2
              · have heq : (2*i, d.cell1.2) = d.cell1 := by ext <;> simp [hc1]
                exact ⟨d.cell1.2, by simp [Domino.cells, heq]⟩
              · have heq : (2*i, d.cell2.2) = d.cell2 := by ext <;> simp [hc2]
                exact ⟨d.cell2.2, by simp [Domino.cells, heq]⟩
            obtain ⟨r, hr_in⟩ := hd_col_cell
            have hd_in_rect := T.dominos_in_rect d hd_mem'
            have h_in_rect : (2*i, r) ∈ Rectangle n 3 := hd_in_rect hr_in
            rw [mem_Rectangle] at h_in_rect
            have hr_range : r = 1 ∨ r = 2 ∨ r = 3 := by omega
            rcases hr_range with hr1 | hr2 | hr3
            · -- (2i, 1) is covered by d_base
              subst hr1
              have heq := T.cell_covered_unique (2*i, 1) d d_base hd_mem' hd_base_mem hr_in
                (by rw [hd_base_cells']; simp)
              rw [heq] at hd_maxCol_ge
              have hbase_max := maxCol_eq_c_add_1_of_cells_eq_c1_c_add_1_1 (2*i - 1) d_base hd_base_cells
              omega
            · -- (2i, 2) is covered by d_mid
              subst hr2
              have heq := T.cell_covered_unique (2*i, 2) d d_mid hd_mem' hd_mid_mem hr_in hd_mid_cov
              rw [heq] at hd_maxCol_ge
              have hmid_minmax := minCol_maxCol_eq_c_of_cells_eq_c2_c3 (2*i) d_mid h_vert_up
              omega
            · -- (2i, 3) is covered by d_mid (since d_mid = {(2i, 2), (2i, 3)})
              subst hr3
              have h_in_mid : (2*i, 3) ∈ d_mid.cells := by rw [h_vert_up]; simp
              have heq := T.cell_covered_unique (2*i, 3) d d_mid hd_mem' hd_mid_mem hr_in h_in_mid
              rw [heq] at hd_maxCol_ge
              have hmid_minmax := minCol_maxCol_eq_c_of_cells_eq_c2_c3 (2*i) d_mid h_vert_up
              omega
          -- But T is faultfree
          exact hfree (2*i) (by omega) (by omega) hfault

      -- Now for the top domino covering (2i, 3)
      have h_cell_top_in : (2*i, 3) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
      obtain ⟨d_top', hd_top'_mem, hd_top'_cov⟩ := T.cell_covered (2*i, 3) h_cell_top_in

      -- d_top' can't cover (2i-1, 3) - that's in d_top_prev
      have hd_top'_not_left : (2*i - 1, 3) ∉ d_top'.cells := by
        intro h_in_top'
        have h_in_prev : (2*i - 1, 3) ∈ d_top_prev.cells := by rw [hprev_top_simp]; simp
        have heq := T.cell_covered_unique (2*i - 1, 3) d_top' d_top_prev hd_top'_mem hd_top_prev_mem h_in_top' h_in_prev
        rw [heq, hprev_top_simp] at hd_top'_cov
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_top'_cov
        obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hd_top'_cov <;> omega

      -- Use domino_at_c3_options to classify d_top'
      have hd_top'_in_rect := T.dominos_in_rect d_top' hd_top'_mem
      have h_top_opts := domino_at_c3_options n (2*i) d_top' hc_mid_ge hc_mid_lt 
        hd_top'_in_rect hd_top'_cov hd_top'_not_left

      have hd_top'_cells : d_top'.cells = {(2*i, 3), (2*i + 1, 3)} := by
        rcases h_top_opts with h_horiz | h_vert
        · exact h_horiz
        · -- Case {(2i, 2), (2i, 3)}: d_top' covers (2i, 2), but d_mid also covers (2i, 2)
          exfalso
          have h_in_top' : (2*i, 2) ∈ d_top'.cells := by rw [h_vert]; simp
          have heq := T.cell_covered_unique (2*i, 2) d_top' d_mid hd_top'_mem hd_mid_mem h_in_top' hd_mid_cov
          rw [heq, hd_mid_cells] at h_vert
          have hmem : (2*i, 3) ∈ ({(2*i, 2), (2*i + 1, 2)} : Finset Cell) := by rw [h_vert]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
          obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hmem <;> omega

      exact ⟨⟨d_base, hd_base_mem, hd_base_cells'⟩,
             ⟨d_mid, hd_mid_mem, hd_mid_cells⟩,
             ⟨d_top', hd_top'_mem, hd_top'_cells⟩⟩


-- created on 2026-10-20
