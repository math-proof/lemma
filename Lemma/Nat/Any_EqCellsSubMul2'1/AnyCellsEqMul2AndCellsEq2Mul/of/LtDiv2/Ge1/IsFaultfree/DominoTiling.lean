import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings
import Lemma.Nat.AnyInCells.of.InRectangle.Cell.DominoTiling
import Lemma.Nat.CellsEq1.of.Ge2.DominoTiling
import Lemma.Nat.Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling
import Lemma.Nat.IffIn_RectangleGe1AndGe_1AndGe21AndGe_2
import Lemma.Nat.DominoTilings.maxCol_eq_c_add_1_of_cells_eq_c1_c_add_1_1
import Lemma.Nat.DominoTilings.minCol_maxCol_eq_2_of_cells_eq_22_23
import Lemma.Nat.DominoTilings.minCol_maxCol_eq_c_of_cells_eq_c2_c3
import Lemma.Nat.DominoTilings.maxCol_eq_2_of_cells_eq_11_21
import Lemma.Nat.DominoTilings.domino_at_c1_forced_right
import Lemma.Nat.DominoTilings.domino_at_22_options
import Lemma.Nat.DominoTilings.domino_at_23_options
import Lemma.Nat.DominoTilings.domino_at_c2_options
import Lemma.Nat.DominoTilings.domino_at_c3_options
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
  (n : ℕ)
  (T : DominoTiling n 3)
  (i : ℕ)
  (hfree : T.isFaultfree)
  (htop : T.hasTopVerticalInCol 1)
  (hi_pos : i ≥ 1)
  (hi_lt : i < n / 2) :
-- imply
  (∃ d ∈ T.dominos, d.cells = {(2*i - 1, 1), (2*i, 1)}) ∧
      (∃ d ∈ T.dominos, d.cells = {(2*i, 2), (2*i + 1, 2)}) ∧
      (∃ d ∈ T.dominos, d.cells = {(2*i, 3), (2*i + 1, 3)}) := by
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
    obtain hi_eq | hi_gt := Nat.eq_or_lt_of_le hi_pos
    ·
      -- Base case: i = 1
      subst hi_eq
      simp only [Nat.mul_one, Nat.reduceSubDiff]
      -- From hi_lt : 1 < n / 2, we get n ≥ 4
      have hn_ge_2 : n ≥ 2 := by omega
      -- Get basement domino from CellsEq1.of.Ge2.DominoTiling
      obtain ⟨d_base, hd_base_mem, hd_base_cells⟩ := CellsEq1.of.Ge2.DominoTiling n T htop hn_ge_2
      -- Get the top vertical domino info
      obtain ⟨d_top, hd_top_mem, hd_top_vert, hd_top_col, hd_top_rows⟩ := htop
      -- The top vertical covers (1, 2) and (1, 3)
      have hd_top_c2_col : d_top.cell2.1 = 1 := hd_top_vert.symm.trans hd_top_col
      have hd_top_covers_12 : (1, 2) ∈ d_top.cells := by
        --
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        obtain ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩ := hd_top_rows
        ·
          left
          ext
          exact hd_top_col.symm
          omega
        ·
          right
          ext
          exact hd_top_c2_col.symm
          omega
      have hd_top_covers_13 : (1, 3) ∈ d_top.cells := by
        --
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        obtain ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩ := hd_top_rows
        ·
          right
          ext
          exact hd_top_c2_col.symm
          omega
        ·
          left
          ext
          exact hd_top_col.symm
          omega
      -- Cell (2, 2) must be covered by some domino d_mid
      have h22_in : (2, 2) ∈ Rectangle n 3 := by rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2]; omega
      obtain ⟨d_mid, hd_mid_mem, hd_mid_cov⟩ := AnyInCells.of.InRectangle.Cell.DominoTiling T (2, 2) h22_in
      -- d_mid doesn't cover (1, 2) (that's covered by d_top)
      have hd_mid_ne_top : d_mid ≠ d_top := by
        --
        intro heq
        subst heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd_mid_cov
        obtain h | h := hd_mid_cov
        ·
          have hcol : d_mid.cell1.1 = 2 := by rw [← h]
          rw [hd_top_col] at hcol
          omega
        ·
          have hcol : d_mid.cell2.1 = 2 := by rw [← h]
          rw [hd_top_c2_col] at hcol
          omega
      have hd_mid_not_12 : (1, 2) ∉ d_mid.cells := by
        --
        intro h12
        exact hd_mid_ne_top (Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (1, 2) d_mid d_top hd_mid_mem hd_top_mem h12 hd_top_covers_12)
      -- The middle domino must be horizontal going right: {(2,2), (3,2)}
      -- (vertical would create fault at col 2, horizontal left blocked by top vertical at (1,2))
      have hd_mid_cells : d_mid.cells = {(2, 2), (3, 2)} := by
        --
        have hn_ge_3 : n ≥ 3 := by omega
        have hd_mid_in_rect := T.dominos_in_rect d_mid hd_mid_mem
        have h_opts := _root_.Nat.DominoTilings.domino_at_22_options n d_mid hd_mid_in_rect hd_mid_cov hd_mid_not_12
        obtain h_horiz | h_vert_down | h_vert_up := h_opts
        ·
          exact h_horiz
        ·
          -- Case {(2, 1), (2, 2)}: d_mid covers (2, 1), but d_base also covers (2, 1)
          exfalso
          have h21_in_mid : (2, 1) ∈ d_mid.cells := by rw [h_vert_down]; simp
          have h21_in_base : (2, 1) ∈ d_base.cells := by rw [hd_base_cells]; simp
          have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2, 1) d_mid d_base hd_mid_mem hd_base_mem h21_in_mid h21_in_base
          rw [heq, hd_base_cells] at h_vert_down
          have : (2, 2) ∈ ({(1, 1), (2, 1)} : Finset Cell) := by rw [h_vert_down]; simp
          simp at this
        ·
          -- Case {(2, 2), (2, 3)}: Creates fault at column 2
          exfalso
          -- Show that no domino in T spans column 2
          refine hfree 2 (by omega) (by omega) ?_
          ·
            --
            constructor
            ·
              omega
            constructor
            ·
              omega
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
                --
                unfold Domino.isHorizontal
                obtain ⟨hcol, _⟩ | ⟨hrow, _⟩ := d.adjacent
                ·
                  -- vertical: minCol = maxCol, but we have minCol ≤ 2 < 3 ≤ maxCol
                  simp only [Domino.minCol, Domino.maxCol] at hmin hmax
                  have : d.cell1.1 = d.cell2.1 := hcol
                  omega
                ·
                  exact hrow
              -- d is horizontal with minCol ≤ 2 < maxCol
              simp only [Domino.minCol, Domino.maxCol] at hmin hmax
              -- Since d is horizontal and adjacent, |cell1.1 - cell2.1| = 1
              have hadj : d.cell1.1 + 1 = d.cell2.1 ∨ d.cell2.1 + 1 = d.cell1.1 := by
                --
                obtain ⟨hvert, _⟩ | ⟨_, hcol⟩ := d.adjacent
                ·
                  -- vertical case: contradicts that d is horizontal
                  exfalso
                  simp only [Domino.isHorizontal] at hd_horiz
                  -- hvert says columns are equal, but hmin ≤ 2 < hmax means columns differ
                  omega
                ·
                  exact hcol
              have hc1_or_c2 : d.cell1.1 = 2 ∨ d.cell2.1 = 2 := by
                --
                obtain h | h := hadj
                ·
                  -- d.cell1.1 + 1 = d.cell2.1
                  have ha_le :
                    d.cell1.1 ≤ 2 := by simp only [min_def] at hmin; split_ifs at hmin <;> omega
                  have hb_gt :
                    d.cell2.1 > 2 := by simp only [max_def] at hmax; split_ifs at hmax <;> omega
                  left; omega
                ·
                  -- d.cell2.1 + 1 = d.cell1.1
                  have hb_le :
                    d.cell2.1 ≤ 2 := by simp only [min_def] at hmin; split_ifs at hmin <;> omega
                  have ha_gt :
                    d.cell1.1 > 2 := by simp only [max_def] at hmax; split_ifs at hmax <;> omega
                  right; omega
              obtain hc1 | hc2 := hc1_or_c2
              ·
                exact ⟨d.cell1.2, by simp [Domino.cells, (show (2, d.cell1.2) = d.cell1 by ext <;> simp [hc1])]⟩
              ·
                exact ⟨d.cell2.2, by simp [Domino.cells, (show (2, d.cell2.2) = d.cell2 by ext <;> simp [hc2])]⟩
            obtain ⟨r, hr_in⟩ := hd_col2_cell
            -- (2, r) is in column 2, so r ∈ {1, 2, 3}
            have hd_in_rect := T.dominos_in_rect d hd_mem'
            have h2r_in_rect : (2, r) ∈ Rectangle n 3 := hd_in_rect hr_in
            rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at h2r_in_rect
            have hr_range : r = 1 ∨ r = 2 ∨ r = 3 := by omega
            obtain hr1 | hr2 | hr3 := hr_range
            ·
              -- (2, 1) is covered by d_base
              subst hr1
              have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2, 1) d d_base hd_mem' hd_base_mem hr_in
                (by rw [hd_base_cells]; simp)
              rw [heq] at hd_maxCol_ge_3
              have hbase_max : d_base.maxCol = 2 := _root_.Nat.DominoTilings.maxCol_eq_2_of_cells_eq_11_21 d_base hd_base_cells
              omega
            ·
              -- (2, 2) is covered by d_mid
              subst hr2
              have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2, 2) d d_mid hd_mem' hd_mid_mem hr_in hd_mid_cov
              rw [heq] at hd_maxCol_ge_3
              have hmid_minmax := _root_.Nat.DominoTilings.minCol_maxCol_eq_2_of_cells_eq_22_23 d_mid h_vert_up
              omega
            ·
              -- (2, 3) is covered by d_mid (since d_mid = {(2,2), (2,3)})
              subst hr3
              have h23_in_mid : (2, 3) ∈ d_mid.cells := by rw [h_vert_up]; simp
              have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2, 3) d d_mid hd_mem' hd_mid_mem hr_in h23_in_mid
              rw [heq] at hd_maxCol_ge_3
              have hmid_minmax := _root_.Nat.DominoTilings.minCol_maxCol_eq_2_of_cells_eq_22_23 d_mid h_vert_up
              omega
          -- But T is faultfree
      -- Similarly for top domino covering (2, 3)
      have h23_in : (2, 3) ∈ Rectangle n 3 := by rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2]; omega
      obtain ⟨d_top', hd_top'_mem, hd_top'_cov⟩ := AnyInCells.of.InRectangle.Cell.DominoTiling T (2, 3) h23_in
      have hd_top'_ne_top : d_top' ≠ d_top := by
        --
        intro heq
        subst heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd_top'_cov
        obtain h | h := hd_top'_cov
        ·
          have hcol : d_top'.cell1.1 = 2 := by rw [← h]
          rw [hd_top_col] at hcol
          omega
        ·
          have hcol : d_top'.cell2.1 = 2 := by rw [← h]
          rw [hd_top_c2_col] at hcol
          omega
      have hd_top'_not_13 : (1, 3) ∉ d_top'.cells := by
        --
        intro h13
        exact hd_top'_ne_top (Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (1, 3) d_top' d_top hd_top'_mem hd_top_mem h13 hd_top_covers_13)
      refine ⟨⟨d_base, hd_base_mem, hd_base_cells⟩,
            ⟨d_mid, hd_mid_mem, hd_mid_cells⟩,
            ⟨d_top', hd_top'_mem, ?_⟩⟩
      ·
        --
        have hd_top'_in_rect := T.dominos_in_rect d_top' hd_top'_mem
        have h_opts := _root_.Nat.DominoTilings.domino_at_23_options n d_top' hd_top'_in_rect hd_top'_cov hd_top'_not_13
        obtain h_horiz | h_vert := h_opts
        ·
          exact h_horiz
        ·
          -- Case {(2, 2), (2, 3)}: d_top' covers (2, 2), but d_mid also covers (2, 2)
          -- So d_top' = d_mid, but d_mid.cells = {(2, 2), (3, 2)} ≠ {(2, 2), (2, 3)}
          exfalso
          have h22_in_top' : (2, 2) ∈ d_top'.cells := by rw [h_vert]; simp
          have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2, 2) d_top' d_mid hd_top'_mem hd_mid_mem h22_in_top' hd_mid_cov
          rw [heq, hd_mid_cells] at h_vert
          have : (2, 3) ∈ ({(2, 2), (3, 2)} : Finset Cell) := by rw [h_vert]; simp
          simp at this
    ·
      -- Induction step: i > 1
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
        --
        simp only [Nat.mul_sub_one, Nat.sub_sub] at hd_base_prev_cells
        norm_num at hd_base_prev_cells
        exact hd_base_prev_cells
      have hprev_mid_simp : d_mid_prev.cells = {(2*i - 2, 2), (2*i - 1, 2)} := by
        --
        simp only [Nat.mul_sub_one] at hd_mid_prev_cells
        simp only [h_sub_add] at hd_mid_prev_cells
        exact hd_mid_prev_cells
      have hprev_top_simp : d_top_prev.cells = {(2*i - 2, 3), (2*i - 1, 3)} := by
        --
        simp only [Nat.mul_sub_one] at hd_top_prev_cells
        simp only [h_sub_add] at hd_top_prev_cells
        exact hd_top_prev_cells
      -- Cell (2i-1, 1) must be covered by some domino d_base
      have h_cell_base_in : (2*i - 1, 1) ∈ Rectangle n 3 := by rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2]; omega
      obtain ⟨d_base, hd_base_mem, hd_base_cov⟩ := AnyInCells.of.InRectangle.Cell.DominoTiling T (2*i - 1, 1) h_cell_base_in
      -- d_base can't cover (2i-2, 1) - that's in d_base_prev
      have hd_base_not_left : (2*i - 2, 1) ∉ d_base.cells := by
        --
        intro h_in_base
        have h_in_prev : (2*i - 2, 1) ∈ d_base_prev.cells := by rw [hprev_base_simp]; simp
        have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2*i - 2, 1) d_base d_base_prev hd_base_mem hd_base_prev_mem h_in_base h_in_prev
        rw [heq, hprev_base_simp] at hd_base_cov
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_base_cov
        obtain ⟨h1, _⟩ | ⟨h1, _⟩ := hd_base_cov <;> omega
      -- d_base can't cover (2i-1, 2) - that's in d_mid_prev
      have hd_base_not_up : (2*i - 1, 2) ∉ d_base.cells := by
        --
        intro h_in_base
        have h_in_prev : (2*i - 1, 2) ∈ d_mid_prev.cells := by rw [hprev_mid_simp]; simp
        have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2*i - 1, 2) d_base d_mid_prev hd_base_mem hd_mid_prev_mem h_in_base h_in_prev
        rw [heq, hprev_mid_simp] at hd_base_cov
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_base_cov
        obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hd_base_cov <;> omega
      -- By _root_.Nat.DominoTilings.domino_at_c1_forced_right, d_base must go right
      have hd_base_in_rect := T.dominos_in_rect d_base hd_base_mem
      have hc_ge : 2*i - 1 ≥ 1 := by omega
      have hc_lt : 2*i - 1 < n := by omega
      -- Adjust the cell coordinates for the lemma
      have hd_base_cov' : (2*i - 1, 1) ∈ d_base.cells := hd_base_cov
      have hd_base_not_left' : (2*i - 1 - 1, 1) ∉ d_base.cells := by
        --
        simp only [Nat.sub_sub]; exact hd_base_not_left
      have hd_base_not_up' : (2*i - 1, 2) ∉ d_base.cells := hd_base_not_up
      have hd_base_cells := _root_.Nat.DominoTilings.domino_at_c1_forced_right n (2*i - 1) d_base hc_ge hc_lt 
        hd_base_in_rect hd_base_cov' hd_base_not_left' hd_base_not_up'
      -- Convert back to the form we need
      have hd_base_cells' : d_base.cells = {(2*i - 1, 1), (2*i, 1)} := by
        --
        simp only [Nat.sub_add_cancel (by omega : 2*i ≥ 1)] at hd_base_cells
        exact hd_base_cells
      -- Now for the middle domino covering (2i, 2)
      have h_cell_mid_in : (2*i, 2) ∈ Rectangle n 3 := by rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2]; omega
      obtain ⟨d_mid, hd_mid_mem, hd_mid_cov⟩ := AnyInCells.of.InRectangle.Cell.DominoTiling T (2*i, 2) h_cell_mid_in
      -- d_mid can't cover (2i-1, 2) - that's in d_mid_prev
      have hd_mid_not_left : (2*i - 1, 2) ∉ d_mid.cells := by
        --
        intro h_in_mid
        have h_in_prev : (2*i - 1, 2) ∈ d_mid_prev.cells := by rw [hprev_mid_simp]; simp
        have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2*i - 1, 2) d_mid d_mid_prev hd_mid_mem hd_mid_prev_mem h_in_mid h_in_prev
        rw [heq, hprev_mid_simp] at hd_mid_cov
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_mid_cov
        obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hd_mid_cov <;> omega
      -- Use _root_.Nat.DominoTilings.domino_at_c2_options to classify d_mid
      have hd_mid_in_rect := T.dominos_in_rect d_mid hd_mid_mem
      have hc_mid_ge : 2*i ≥ 1 := by omega
      have hc_mid_lt : 2*i < n := by omega
      have hd_mid_not_left' : (2*i - 1, 2) ∉ d_mid.cells := hd_mid_not_left
      have h_mid_opts := _root_.Nat.DominoTilings.domino_at_c2_options n (2*i) d_mid hc_mid_ge hc_mid_lt 
        hd_mid_in_rect hd_mid_cov hd_mid_not_left'
      have hd_mid_cells : d_mid.cells = {(2*i, 2), (2*i + 1, 2)} := by
        --
        obtain h_horiz | h_vert_down | h_vert_up := h_mid_opts
        ·
          exact h_horiz
        ·
          -- Case {(2i, 1), (2i, 2)}: d_mid covers (2i, 1), but d_base also covers (2i, 1)
          exfalso
          have h_in_mid : (2*i, 1) ∈ d_mid.cells := by rw [h_vert_down]; simp
          have h_in_base : (2*i, 1) ∈ d_base.cells := by rw [hd_base_cells']; simp
          have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2*i, 1) d_mid d_base hd_mid_mem hd_base_mem h_in_mid h_in_base
          rw [heq, hd_base_cells'] at h_vert_down
          have hmem :
            (2*i, 2) ∈ ({(2*i - 1, 1), (2*i, 1)} : Finset Cell) := by rw [h_vert_down]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
          obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hmem <;> omega
        ·
          -- Case {(2i, 2), (2i, 3)}: Creates fault at column 2i
          exfalso
          -- Show that no domino in T spans column 2i
          refine hfree (2*i) (by omega) (by omega) ?_
          ·
            --
            constructor
            ·
              omega
            constructor
            ·
              omega
            intro d hd_mem' ⟨hmin, hmax⟩
            have hd_maxCol_ge : d.maxCol ≥ 2*i + 1 := by omega
            -- d has minCol ≤ 2i and maxCol ≥ 2i+1, so d is horizontal spanning columns 2i and 2i+1
            have hd_col_cell : ∃ r, (2*i, r) ∈ d.cells := by
              --
              have hd_horiz : d.isHorizontal := by
                --
                unfold Domino.isHorizontal
                obtain ⟨hcol, _⟩ | ⟨hrow, _⟩ := d.adjacent
                ·
                  simp only [Domino.minCol, Domino.maxCol] at hmin hmax
                  have : d.cell1.1 = d.cell2.1 := hcol
                  omega
                ·
                  exact hrow
              simp only [Domino.minCol, Domino.maxCol] at hmin hmax
              have hadj : d.cell1.1 + 1 = d.cell2.1 ∨ d.cell2.1 + 1 = d.cell1.1 := by
                --
                obtain ⟨hvert, _⟩ | ⟨_, hcol⟩ := d.adjacent
                ·
                  exfalso
                  simp only [Domino.isHorizontal] at hd_horiz
                  omega
                ·
                  exact hcol
              have hc1_or_c2 : d.cell1.1 = 2*i ∨ d.cell2.1 = 2*i := by
                --
                obtain h | h := hadj
                ·
                  have ha_le :
                    d.cell1.1 ≤ 2*i := by simp only [min_def] at hmin; split_ifs at hmin <;> omega
                  have hb_gt :
                    d.cell2.1 > 2*i := by simp only [max_def] at hmax; split_ifs at hmax <;> omega
                  left; omega
                ·
                  have hb_le :
                    d.cell2.1 ≤ 2*i := by simp only [min_def] at hmin; split_ifs at hmin <;> omega
                  have ha_gt :
                    d.cell1.1 > 2*i := by simp only [max_def] at hmax; split_ifs at hmax <;> omega
                  right; omega
              obtain hc1 | hc2 := hc1_or_c2
              ·
                exact ⟨d.cell1.2, by simp [Domino.cells, (show (2*i, d.cell1.2) = d.cell1 by ext <;> simp [hc1])]⟩
              ·
                exact ⟨d.cell2.2, by simp [Domino.cells, (show (2*i, d.cell2.2) = d.cell2 by ext <;> simp [hc2])]⟩
            obtain ⟨r, hr_in⟩ := hd_col_cell
            have hd_in_rect := T.dominos_in_rect d hd_mem'
            have h_in_rect : (2*i, r) ∈ Rectangle n 3 := hd_in_rect hr_in
            rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at h_in_rect
            have hr_range : r = 1 ∨ r = 2 ∨ r = 3 := by omega
            obtain hr1 | hr2 | hr3 := hr_range
            ·
              -- (2i, 1) is covered by d_base
              subst hr1
              have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2*i, 1) d d_base hd_mem' hd_base_mem hr_in
                (by rw [hd_base_cells']; simp)
              rw [heq] at hd_maxCol_ge
              have hbase_max := _root_.Nat.DominoTilings.maxCol_eq_c_add_1_of_cells_eq_c1_c_add_1_1 (2*i - 1) d_base hd_base_cells
              omega
            ·
              -- (2i, 2) is covered by d_mid
              subst hr2
              have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2*i, 2) d d_mid hd_mem' hd_mid_mem hr_in hd_mid_cov
              rw [heq] at hd_maxCol_ge
              have hmid_minmax := _root_.Nat.DominoTilings.minCol_maxCol_eq_c_of_cells_eq_c2_c3 (2*i) d_mid h_vert_up
              omega
            ·
              -- (2i, 3) is covered by d_mid (since d_mid = {(2i, 2), (2i, 3)})
              subst hr3
              have h_in_mid : (2*i, 3) ∈ d_mid.cells := by rw [h_vert_up]; simp
              have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2*i, 3) d d_mid hd_mem' hd_mid_mem hr_in h_in_mid
              rw [heq] at hd_maxCol_ge
              have hmid_minmax := _root_.Nat.DominoTilings.minCol_maxCol_eq_c_of_cells_eq_c2_c3 (2*i) d_mid h_vert_up
              omega
          -- But T is faultfree
      -- Now for the top domino covering (2i, 3)
      have h_cell_top_in : (2*i, 3) ∈ Rectangle n 3 := by rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2]; omega
      obtain ⟨d_top', hd_top'_mem, hd_top'_cov⟩ := AnyInCells.of.InRectangle.Cell.DominoTiling T (2*i, 3) h_cell_top_in
      -- d_top' can't cover (2i-1, 3) - that's in d_top_prev
      have hd_top'_not_left : (2*i - 1, 3) ∉ d_top'.cells := by
        --
        intro h_in_top'
        have h_in_prev : (2*i - 1, 3) ∈ d_top_prev.cells := by rw [hprev_top_simp]; simp
        have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2*i - 1, 3) d_top' d_top_prev hd_top'_mem hd_top_prev_mem h_in_top' h_in_prev
        rw [heq, hprev_top_simp] at hd_top'_cov
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_top'_cov
        obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hd_top'_cov <;> omega
      -- Use _root_.Nat.DominoTilings.domino_at_c3_options to classify d_top'
      have hd_top'_in_rect := T.dominos_in_rect d_top' hd_top'_mem
      have h_top_opts := _root_.Nat.DominoTilings.domino_at_c3_options n (2*i) d_top' hc_mid_ge hc_mid_lt 
        hd_top'_in_rect hd_top'_cov hd_top'_not_left
      refine ⟨⟨d_base, hd_base_mem, hd_base_cells'⟩,
            ⟨d_mid, hd_mid_mem, hd_mid_cells⟩,
            ⟨d_top', hd_top'_mem, ?_⟩⟩
      ·
        --
        obtain h_horiz | h_vert := h_top_opts
        ·
          exact h_horiz
        ·
          -- Case {(2i, 2), (2i, 3)}: d_top' covers (2i, 2), but d_mid also covers (2i, 2)
          exfalso
          have h_in_top' : (2*i, 2) ∈ d_top'.cells := by rw [h_vert]; simp
          have heq := Eq.of.InCells.InCells.InDominos.InDominos.Domino.Cell.DominoTiling T (2*i, 2) d_top' d_mid hd_top'_mem hd_mid_mem h_in_top' hd_mid_cov
          rw [heq, hd_mid_cells] at h_vert
          have hmem :
            (2*i, 3) ∈ ({(2*i, 2), (2*i + 1, 2)} : Finset Cell) := by rw [h_vert]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
          obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hmem <;> omega


-- created on 2026-10-20
