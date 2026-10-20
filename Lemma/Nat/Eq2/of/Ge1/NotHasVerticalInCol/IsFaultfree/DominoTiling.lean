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
  (n : ℕ)
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree)
  (hno_vert : ¬T.hasVerticalInCol 1)
  (hn : n ≥ 1) :
-- imply
  n = 2 := by
-- proof
  -- Handle edge cases n = 1 and n = 2
  rcases Nat.lt_trichotomy n 2 with hn_lt | hn_eq | hn_gt
  · -- n < 2, so n = 1 (since n ≥ 1)
    have hn1 : n = 1 := by omega
    -- n = 1: No valid tiling exists (3 cells can't be covered by dominos)
    exfalso
    have h := T.card_eq_twice_dominos
    simp only [card_Rectangle, hn1] at h
    omega
  · exact hn_eq  -- n = 2
  · -- n > 2: derive contradiction by showing there's a fault at column 2
    exfalso
    have hn_ge_3 : n ≥ 3 := hn_gt
    -- The key insight: all dominos covering column 1 must be horizontal (no vertical allowed)
    -- and span columns 1-2. This means all cells in column 2 are covered by these dominos.
    -- Any domino with minCol = 2 would overlap with a column-1 domino, contradiction.
    -- So no domino spans columns 2-3, creating a fault at column 2.
    have hfault : T.hasFaultAt 2 := by
      refine ⟨by omega, hn_ge_3, ?_⟩
      intro d hd
      push Not
      intro hmin
      -- hmin : d.minCol ≤ 2, goal: d.maxCol ≤ 2
      have hd_in_rect := T.dominos_in_rect d hd
      have hc1_in_rect : d.cell1 ∈ Rectangle n 3 := hd_in_rect (by simp [Domino.cells])
      have hc2_in_rect : d.cell2 ∈ Rectangle n 3 := hd_in_rect (by simp [Domino.cells])
      rw [mem_Rectangle] at hc1_in_rect hc2_in_rect
      have hcol1_ge : d.cell1.1 ≥ 1 := hc1_in_rect.1
      have hcol2_ge : d.cell2.1 ≥ 1 := hc2_in_rect.1
      -- Case split on whether d touches column 1
      by_cases hmin1 : d.minCol = 1
      · -- d touches column 1: it must be horizontal spanning 1-2
        -- First, find which cell is in column 1
        have hcov1 : ∃ y, (1, y) ∈ d.cells := by
          unfold Domino.minCol at hmin1
          by_cases h : d.cell1.1 ≤ d.cell2.1
          · simp only [min_eq_left h] at hmin1
            exact ⟨d.cell1.2, by simp [Domino.cells]; left; rw [← hmin1]⟩
          · push Not at h
            simp only [min_eq_right (le_of_lt h)] at hmin1
            exact ⟨d.cell2.2, by simp [Domino.cells]; right; rw [← hmin1]⟩
        -- d is not vertical (since no vertical in column 1)
        have hd_novert : ¬d.isVertical := by
          intro hvert
          apply hno_vert
          unfold DominoTiling.hasVerticalInCol
          obtain ⟨y, hy⟩ := hcov1
          simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with h | h
          · exact ⟨d, hd, hvert, by rw [← h]⟩
          · have hc2 : d.cell2.1 = 1 := by rw [← h]
            exact ⟨d, hd, hvert, by unfold Domino.isVertical at hvert; omega⟩
        -- d is horizontal with one cell in column 1, so it spans columns 1-2
        unfold Domino.isVertical at hd_novert
        obtain ⟨hcol_eq, _⟩ | ⟨_, hcol_adj⟩ := d.adjacent
        · exact absurd hcol_eq hd_novert
        · -- d is horizontal, spanning columns 1-2
          unfold Domino.maxCol
          obtain ⟨y, hy⟩ := hcov1
          simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with h | h
          · have hc1 : d.cell1.1 = 1 := by rw [← h]
            rcases hcol_adj with hadj | hadj
            · simp only [hc1] at hadj; omega
            · simp only [hc1] at hadj; omega
          · have hc2 : d.cell2.1 = 1 := by rw [← h]
            rcases hcol_adj with hadj | hadj
            · simp only [hc2] at hadj; omega
            · simp only [hc2] at hadj; omega
      · -- d.minCol ≠ 1, so d.minCol = 2 (since d.minCol ≤ 2 and d.minCol ≥ 1)
        have hmin2 : d.minCol = 2 := by unfold Domino.minCol at hmin hmin1 ⊢; omega
        -- d has a cell in column 2
        unfold Domino.minCol at hmin2
        have hcell2 : d.cell1.1 = 2 ∨ d.cell2.1 = 2 := by
          by_cases h : d.cell1.1 ≤ d.cell2.1
          · left; simp only [min_eq_left h] at hmin2; exact hmin2
          · right; push Not at h; simp only [min_eq_right (le_of_lt h)] at hmin2; exact hmin2
        -- This cell in column 2 is covered by some domino d' that covers column 1
        -- d' must be horizontal spanning 1-2 (since no vertical in column 1)
        -- So d and d' both cover a cell in column 2, contradicting disjointness (unless d = d')
        -- But if d = d', then d.minCol = 1, contradicting hmin2
        rcases hcell2 with hc1_col | hc2_col
        · -- d.cell1 is in column 2
          -- The cell (1, d.cell1.2) is in the rectangle and covered by some domino d'
          have h1r : (1, d.cell1.2) ∈ Rectangle n 3 := by
            rw [mem_Rectangle]
            exact ⟨le_refl 1, by omega, hc1_in_rect.2.2.1, hc1_in_rect.2.2.2⟩
          -- Find the domino d' that covers (1, d.cell1.2)
          obtain ⟨d', hd'_mem, hd'_cov⟩ := T.cell_covered (1, d.cell1.2) h1r
          have hd'_min_le : d'.minCol ≤ 1 := by
            unfold Domino.minCol
            simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd'_cov
            rcases hd'_cov with h | h
            · simp only [← h]; exact min_le_left _ _
            · simp only [← h]; exact min_le_right _ _
          have hd'_in_rect := T.dominos_in_rect d' hd'_mem
          have hd'_c1_in : d'.cell1 ∈ Rectangle n 3 := hd'_in_rect (by simp [Domino.cells])
          have hd'_c2_in : d'.cell2 ∈ Rectangle n 3 := hd'_in_rect (by simp [Domino.cells])
          rw [mem_Rectangle] at hd'_c1_in hd'_c2_in
          have hd'_col1_ge : d'.cell1.1 ≥ 1 := hd'_c1_in.1
          have hd'_col2_ge : d'.cell2.1 ≥ 1 := hd'_c2_in.1
          have hd'_min_eq : d'.minCol = 1 := by unfold Domino.minCol at hd'_min_le ⊢; omega
          have hd'_cov1 : ∃ y, (1, y) ∈ d'.cells := by
            unfold Domino.minCol at hd'_min_eq
            by_cases h : d'.cell1.1 ≤ d'.cell2.1
            · simp only [min_eq_left h] at hd'_min_eq
              exact ⟨d'.cell1.2, by simp [Domino.cells]; left; rw [← hd'_min_eq]⟩
            · push Not at h
              simp only [min_eq_right (le_of_lt h)] at hd'_min_eq
              exact ⟨d'.cell2.2, by simp [Domino.cells]; right; rw [← hd'_min_eq]⟩
          have hd'_novert : ¬d'.isVertical := by
            intro hvert
            apply hno_vert
            unfold DominoTiling.hasVerticalInCol
            obtain ⟨y, hy⟩ := hd'_cov1
            simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with h | h
            · exact ⟨d', hd'_mem, hvert, by rw [← h]⟩
            · have hc2' : d'.cell2.1 = 1 := by rw [← h]
              exact ⟨d', hd'_mem, hvert, by unfold Domino.isVertical at hvert; omega⟩
          unfold Domino.isVertical at hd'_novert
          obtain ⟨hcol_eq, _⟩ | ⟨hrow_eq, hcol_adj⟩ := d'.adjacent
          · exact absurd hcol_eq hd'_novert
          · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd'_cov
            rcases hd'_cov with hcov | hcov
            · have hd'c1 : d'.cell1 = (1, d.cell1.2) := hcov.symm
              have hd'c2_row : d'.cell2.2 = d.cell1.2 := by
                have h1 : d'.cell1.2 = d.cell1.2 := by rw [hd'c1]
                exact hrow_eq.symm.trans h1
              have hd'c2_col : d'.cell2.1 = 2 := by
                have h1 : d'.cell1.1 = 1 := by rw [hd'c1]
                rcases hcol_adj with hadj | hadj
                · omega
                · omega
              have hd'c2_eq : d'.cell2 = d.cell1 := by
                ext <;> [exact hd'c2_col.trans hc1_col.symm; exact hd'c2_row]
              by_cases hdd' : d = d'
              · rw [hdd'] at hmin2
                have : d'.minCol = 1 := hd'_min_eq
                simp only [Domino.minCol] at this hmin2
                omega
              · have hd_cov : d.cell1 ∈ d.cells := by simp [Domino.cells]
                have hd'_cov' : d.cell1 ∈ d'.cells := by simp [Domino.cells, hd'c2_eq]
                have hdisj := T.pairwise_disjoint d hd d' hd'_mem hdd'
                rw [Finset.disjoint_iff_ne] at hdisj
                exact absurd rfl (hdisj d.cell1 hd_cov d.cell1 hd'_cov')
            · have hd'c2 : d'.cell2 = (1, d.cell1.2) := hcov.symm
              have hd'c1_row : d'.cell1.2 = d.cell1.2 := by
                have h2 : d'.cell2.2 = d.cell1.2 := by rw [hd'c2]
                exact hrow_eq.trans h2
              have hd'c1_col : d'.cell1.1 = 2 := by
                have h2 : d'.cell2.1 = 1 := by rw [hd'c2]
                rcases hcol_adj with hadj | hadj
                · omega
                · omega
              have hd'c1_eq : d'.cell1 = d.cell1 := by
                ext <;> [exact hd'c1_col.trans hc1_col.symm; exact hd'c1_row]
              by_cases hdd' : d = d'
              · rw [hdd'] at hmin2
                have : d'.minCol = 1 := hd'_min_eq
                simp only [Domino.minCol] at this hmin2
                omega
              · have hd_cov : d.cell1 ∈ d.cells := by simp [Domino.cells]
                have hd'_cov' : d.cell1 ∈ d'.cells := by simp [Domino.cells, hd'c1_eq]
                have hdisj := T.pairwise_disjoint d hd d' hd'_mem hdd'
                rw [Finset.disjoint_iff_ne] at hdisj
                exact absurd rfl (hdisj d.cell1 hd_cov d.cell1 hd'_cov')
        · -- d.cell2 is in column 2 (similar argument)
          have h1r : (1, d.cell2.2) ∈ Rectangle n 3 := by
            rw [mem_Rectangle]
            exact ⟨le_refl 1, by omega, hc2_in_rect.2.2.1, hc2_in_rect.2.2.2⟩
          obtain ⟨d', hd'_mem, hd'_cov⟩ := T.cell_covered (1, d.cell2.2) h1r
          have hd'_min_le : d'.minCol ≤ 1 := by
            unfold Domino.minCol
            simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd'_cov
            rcases hd'_cov with h | h
            · simp only [← h]; exact min_le_left _ _
            · simp only [← h]; exact min_le_right _ _
          have hd'_in_rect := T.dominos_in_rect d' hd'_mem
          have hd'_c1_in : d'.cell1 ∈ Rectangle n 3 := hd'_in_rect (by simp [Domino.cells])
          have hd'_c2_in : d'.cell2 ∈ Rectangle n 3 := hd'_in_rect (by simp [Domino.cells])
          rw [mem_Rectangle] at hd'_c1_in hd'_c2_in
          have hd'_col1_ge : d'.cell1.1 ≥ 1 := hd'_c1_in.1
          have hd'_col2_ge : d'.cell2.1 ≥ 1 := hd'_c2_in.1
          have hd'_min_eq : d'.minCol = 1 := by unfold Domino.minCol at hd'_min_le ⊢; omega
          have hd'_cov1 : ∃ y, (1, y) ∈ d'.cells := by
            unfold Domino.minCol at hd'_min_eq
            by_cases h : d'.cell1.1 ≤ d'.cell2.1
            · simp only [min_eq_left h] at hd'_min_eq
              exact ⟨d'.cell1.2, by simp [Domino.cells]; left; rw [← hd'_min_eq]⟩
            · push Not at h
              simp only [min_eq_right (le_of_lt h)] at hd'_min_eq
              exact ⟨d'.cell2.2, by simp [Domino.cells]; right; rw [← hd'_min_eq]⟩
          have hd'_novert : ¬d'.isVertical := by
            intro hvert
            apply hno_vert
            unfold DominoTiling.hasVerticalInCol
            obtain ⟨y, hy⟩ := hd'_cov1
            simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with h | h
            · exact ⟨d', hd'_mem, hvert, by rw [← h]⟩
            · have hc2' : d'.cell2.1 = 1 := by rw [← h]
              exact ⟨d', hd'_mem, hvert, by unfold Domino.isVertical at hvert; omega⟩
          unfold Domino.isVertical at hd'_novert
          obtain ⟨hcol_eq, _⟩ | ⟨hrow_eq, hcol_adj⟩ := d'.adjacent
          · exact absurd hcol_eq hd'_novert
          · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd'_cov
            rcases hd'_cov with hcov | hcov
            · have hd'c1 : d'.cell1 = (1, d.cell2.2) := hcov.symm
              have hd'c2_row : d'.cell2.2 = d.cell2.2 := by
                have h1 : d'.cell1.2 = d.cell2.2 := by rw [hd'c1]
                exact hrow_eq.symm.trans h1
              have hd'c2_col : d'.cell2.1 = 2 := by
                have h1 : d'.cell1.1 = 1 := by rw [hd'c1]
                rcases hcol_adj with hadj | hadj
                · omega
                · omega
              have hd'c2_eq : d'.cell2 = d.cell2 := by
                ext <;> [exact hd'c2_col.trans hc2_col.symm; exact hd'c2_row]
              by_cases hdd' : d = d'
              · rw [hdd'] at hmin2
                have : d'.minCol = 1 := hd'_min_eq
                simp only [Domino.minCol] at this hmin2
                omega
              · have hd_cov : d.cell2 ∈ d.cells := by simp [Domino.cells]
                have hd'_cov' : d.cell2 ∈ d'.cells := by simp [Domino.cells, hd'c2_eq]
                have hdisj := T.pairwise_disjoint d hd d' hd'_mem hdd'
                rw [Finset.disjoint_iff_ne] at hdisj
                exact absurd rfl (hdisj d.cell2 hd_cov d.cell2 hd'_cov')
            · have hd'c2 : d'.cell2 = (1, d.cell2.2) := hcov.symm
              have hd'c1_row : d'.cell1.2 = d.cell2.2 := by
                have h2 : d'.cell2.2 = d.cell2.2 := by rw [hd'c2]
                exact hrow_eq.trans h2
              have hd'c1_col : d'.cell1.1 = 2 := by
                have h2 : d'.cell2.1 = 1 := by rw [hd'c2]
                rcases hcol_adj with hadj | hadj
                · omega
                · omega
              have hd'c1_eq : d'.cell1 = d.cell2 := by
                ext <;> [exact hd'c1_col.trans hc2_col.symm; exact hd'c1_row]
              by_cases hdd' : d = d'
              · rw [hdd'] at hmin2
                have : d'.minCol = 1 := hd'_min_eq
                simp only [Domino.minCol] at this hmin2
                omega
              · have hd_cov : d.cell2 ∈ d.cells := by simp [Domino.cells]
                have hd'_cov' : d.cell2 ∈ d'.cells := by simp [Domino.cells, hd'c1_eq]
                have hdisj := T.pairwise_disjoint d hd d' hd'_mem hdd'
                rw [Finset.disjoint_iff_ne] at hdisj
                exact absurd rfl (hdisj d.cell2 hd_cov d.cell2 hd'_cov')
    exact hfree 2 (by omega) hn_ge_3 hfault


-- created on 2026-10-20
