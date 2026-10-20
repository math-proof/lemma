import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


-- Private helpers (ported from sympy DominoTilings; file-local)

private lemma domino_at_n3_options (n : ℕ) (d : Domino)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (n, 3) ∈ d.cells) :
    d.cells = {(n - 1, 3), (n, 3)} ∨ d.cells = {(n, 2), (n, 3)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov
  rcases h_cov with hc1 | hc2
  · have h2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
    rw [mem_Rectangle] at h2_in
    have hc1_col : d.cell1.1 = n := by rw [← hc1]
    have hc1_row : d.cell1.2 = 3 := by rw [← hc1]
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · right; simp only [Domino.cells]
      have hc2_col : d.cell2.1 = n := by rw [← hcol, hc1_col]
      rcases hrow with hr | hr
      · exfalso; omega
      · have hc2_row : d.cell2.2 = 2 := by omega
        have h2_eq : d.cell2 = (n, 2) := Prod.ext hc2_col hc2_row
        rw [← hc1, h2_eq, Finset.pair_comm]
    · left; simp only [Domino.cells]
      have hc2_row : d.cell2.2 = 3 := by rw [← hrow, hc1_row]
      rcases hcol with hc | hc
      · exfalso; omega
      · have hc2_col : d.cell2.1 = n - 1 := by omega
        have h2_eq : d.cell2 = (n - 1, 3) := Prod.ext hc2_col hc2_row
        rw [← hc1, h2_eq, Finset.pair_comm]
  · have h1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
    rw [mem_Rectangle] at h1_in
    have hc2_col : d.cell2.1 = n := by rw [← hc2]
    have hc2_row : d.cell2.2 = 3 := by rw [← hc2]
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · right; simp only [Domino.cells]
      have hc1_col : d.cell1.1 = n := by rw [hcol, hc2_col]
      rcases hrow with hr | hr
      · have hc1_row : d.cell1.2 = 2 := by omega
        have h1_eq : d.cell1 = (n, 2) := Prod.ext hc1_col hc1_row
        rw [← hc2, h1_eq]
      · exfalso; omega
    · left; simp only [Domino.cells]
      have hc1_row : d.cell1.2 = 3 := by rw [hrow, hc2_row]
      rcases hcol with hc | hc
      · have hc1_col : d.cell1.1 = n - 1 := by omega
        have h1_eq : d.cell1 = (n - 1, 3) := Prod.ext hc1_col hc1_row
        rw [← hc2, h1_eq]
      · exfalso; omega

private lemma domino_at_n1_options (n : ℕ) (d : Domino)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (n, 1) ∈ d.cells) :
    d.cells = {(n - 1, 1), (n, 1)} ∨ d.cells = {(n, 1), (n, 2)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov
  rcases h_cov with hc1 | hc2
  · have h2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
    rw [mem_Rectangle] at h2_in
    have hc1_col : d.cell1.1 = n := by rw [← hc1]
    have hc1_row : d.cell1.2 = 1 := by rw [← hc1]
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · right; simp only [Domino.cells]
      have hc2_col : d.cell2.1 = n := by rw [← hcol, hc1_col]
      rcases hrow with hr | hr
      · have hc2_row : d.cell2.2 = 2 := by omega
        have h2_eq : d.cell2 = (n, 2) := Prod.ext hc2_col hc2_row
        rw [← hc1, h2_eq]
      · exfalso; omega
    · left; simp only [Domino.cells]
      have hc2_row : d.cell2.2 = 1 := by rw [← hrow, hc1_row]
      rcases hcol with hc | hc
      · exfalso; omega
      · have hc2_col : d.cell2.1 = n - 1 := by omega
        have h2_eq : d.cell2 = (n - 1, 1) := Prod.ext hc2_col hc2_row
        rw [← hc1, h2_eq, Finset.pair_comm]
  · have h1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
    rw [mem_Rectangle] at h1_in
    have hc2_col : d.cell2.1 = n := by rw [← hc2]
    have hc2_row : d.cell2.2 = 1 := by rw [← hc2]
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · right; simp only [Domino.cells]
      have hc1_col : d.cell1.1 = n := by rw [hcol, hc2_col]
      rcases hrow with hr | hr
      · exfalso; omega
      · have hc1_row : d.cell1.2 = 2 := by omega
        have h1_eq : d.cell1 = (n, 2) := Prod.ext hc1_col hc1_row
        rw [← hc2, h1_eq, Finset.pair_comm]
    · left; simp only [Domino.cells]
      have hc1_row : d.cell1.2 = 1 := by rw [hrow, hc2_row]
      rcases hcol with hc | hc
      · have hc1_col : d.cell1.1 = n - 1 := by omega
        have h1_eq : d.cell1 = (n - 1, 1) := Prod.ext hc1_col hc1_row
        rw [← hc2, h1_eq]
      · exfalso; omega

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree)
  (htop : T.hasTopVerticalInCol 1) :
-- imply
  Even n ∧ ∃ (hn : Even n) (hn_ge : n ≥ 2), DominoTiling.TilingEquiv T (TilingA n hn hn_ge) := by
-- proof
  have hn_even := claim2_n_even n T hfree htop
  have hn_ge := faultfree_hasTopVerticalInCol_implies_n_ge_two n T hfree htop
  refine ⟨hn_even, hn_even, hn_ge, ?_⟩
  -- The uniqueness proof: TilingEquiv T (TilingA n hn_even hn_ge)
  -- TilingEquiv means T.dominos.image Domino.cells = TilingA.dominos.image Domino.cells
  -- This is easier than showing T.dominos = TilingA.dominos because we don't need
  -- exact cell ordering within each domino.
  unfold DominoTiling.TilingEquiv
  -- Both tilings cover the same rectangle, so they have the same number of dominos
  have h_card_T := T.card_eq_twice_dominos
  have h_card_A := (TilingA n hn_even hn_ge).card_eq_twice_dominos
  simp only [card_Rectangle] at h_card_T h_card_A
  have h_card_eq : T.dominos.card = (TilingA n hn_even hn_ge).dominos.card := by omega
  -- Both tilings cover the same cells (the rectangle), so their cell images are equal
  -- We show this by showing each covers all cells of the rectangle
  have hT_cells : T.dominos.biUnion Domino.cells = Rectangle n 3 := T.covers_all
  have hA_cells : (TilingA n hn_even hn_ge).dominos.biUnion Domino.cells = Rectangle n 3 :=
    (TilingA n hn_even hn_ge).covers_all
  -- The image of cells is the set of all cell-pairs covered
  -- Since both tilings partition the same rectangle, their cell images are determined
  -- by which cells are covered together (as dominos)
  -- For a tiling, each cell appears in exactly one domino, so the image is a partition
  -- Two partitions of the same set with the same number of parts must have parts of
  -- the same sizes (all size 2 for dominos), but not necessarily the same parts
  -- However, we can show the parts are the same by using the structure of the tilings
  -- Strategy: We show both sets are equal by showing one is a subset of the other
  -- and they have the same cardinality.
  -- Key insight: in a tiling, Domino.cells is injective because different dominos have disjoint cells
  have h_cells_inj_T : ∀ d₁ ∈ T.dominos, ∀ d₂ ∈ T.dominos, d₁.cells = d₂.cells → d₁ = d₂ := by
    intro d₁ hd₁ d₂ hd₂ h_eq
    by_contra hne
    have h_disj := T.pairwise_disjoint d₁ hd₁ d₂ hd₂ hne
    rw [Finset.disjoint_iff_ne] at h_disj
    have h_cell1 : d₁.cell1 ∈ d₁.cells := by simp [Domino.cells]
    have h_cell1' : d₁.cell1 ∈ d₂.cells := by rw [← h_eq]; exact h_cell1
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cell1'
    rcases h_cell1' with h | h
    · have h_mem : d₁.cell1 ∈ d₂.cells := by simp [Domino.cells, h]
      exact h_disj d₁.cell1 h_cell1 d₁.cell1 h_mem rfl
    · have h_mem : d₁.cell1 ∈ d₂.cells := by simp [Domino.cells, h]
      exact h_disj d₁.cell1 h_cell1 d₁.cell1 h_mem rfl
  have h_cells_inj_A : ∀ d₁ ∈ (TilingA n hn_even hn_ge).dominos,
      ∀ d₂ ∈ (TilingA n hn_even hn_ge).dominos, d₁.cells = d₂.cells → d₁ = d₂ := by
    intro d₁ hd₁ d₂ hd₂ h_eq
    by_contra hne
    have h_disj := (TilingA n hn_even hn_ge).pairwise_disjoint d₁ hd₁ d₂ hd₂ hne
    rw [Finset.disjoint_iff_ne] at h_disj
    have h_cell1 : d₁.cell1 ∈ d₁.cells := by simp [Domino.cells]
    have h_cell1' : d₁.cell1 ∈ d₂.cells := by rw [← h_eq]; exact h_cell1
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cell1'
    rcases h_cell1' with h | h
    · have h_mem : d₁.cell1 ∈ d₂.cells := by simp [Domino.cells, h]
      exact h_disj d₁.cell1 h_cell1 d₁.cell1 h_mem rfl
    · have h_mem : d₁.cell1 ∈ d₂.cells := by simp [Domino.cells, h]
      exact h_disj d₁.cell1 h_cell1 d₁.cell1 h_mem rfl
  -- Prove the backward direction: TilingA.dominos.image Domino.cells ⊆ T.dominos.image Domino.cells
  have h_backward : (TilingA n hn_even hn_ge).dominos.image Domino.cells ⊆ T.dominos.image Domino.cells := by
    intro S hS
    rw [Finset.mem_image] at hS ⊢
    obtain ⟨d, hd_mem, hd_cells⟩ := hS
    -- d is a domino in TilingA, we need to find a domino in T with the same cells
    change d ∈ basementDominos n ∪ {leftWall} ∪ {rightWall n} ∪ middleDominos n ∪ topDominos n at hd_mem
    simp only [Finset.mem_union, Finset.mem_singleton] at hd_mem
    rcases hd_mem with ((((hd | hd) | hd) | hd) | hd)
    · -- d ∈ basementDominos n
      simp only [basementDominos, Finset.mem_map, Finset.mem_range] at hd
      obtain ⟨j, hj_lt, hd_eq⟩ := hd
      have hd_cell1 : d.cell1 = (2 * j + 1, 1) := by
        simp only [← Function.Embedding.toFun_eq_coe] at hd_eq; rw [← hd_eq]
      have hd_cell2 : d.cell2 = (2 * j + 2, 1) := by
        simp only [← Function.Embedding.toFun_eq_coe] at hd_eq; rw [← hd_eq]
      by_cases hj : j < n / 2 - 1
      · -- j < n/2 - 1: use claim1 with i = j + 1
        have hi_pos : j + 1 ≥ 1 := by omega
        have hi_lt : j + 1 < n / 2 := by omega
        obtain ⟨⟨d', hd'_mem, hd'_cells⟩, _, _⟩ :=
          claim1_basement_middle_top n T hfree htop (j + 1) hi_pos hi_lt
        use d', hd'_mem
        rw [← hd_cells]
        simp only [Domino.cells, hd_cell1, hd_cell2]
        -- Need to show: {(2 * j + 1, 1), (2 * j + 2, 1)} = {(2 * (j + 1) - 1, 1), (2 * (j + 1), 1)}
        -- which simplifies to the same set since 2*(j+1)-1 = 2*j+1 and 2*(j+1) = 2*j+2
        convert hd'_cells using 2 <;> (try simp [Domino.cells]; try omega)
      · -- j = n/2 - 1: last basement domino (n-1, 1) - (n, 1)
        have hj_eq : j = n / 2 - 1 := by omega
        have hd_c1 : d.cell1 = (n - 1, 1) := by
          rw [hd_cell1, hj_eq]
          obtain ⟨k, hk⟩ := hn_even; subst hk
          have hkk : (k + k) / 2 = k := by omega
          simp only [hkk]; ext <;> omega
        have hd_c2 : d.cell2 = (n, 1) := by
          rw [hd_cell2, hj_eq]
          obtain ⟨k, hk⟩ := hn_even; subst hk
          have hkk : (k + k) / 2 = k := by omega
          simp only [hkk]; ext <;> omega
        have hn3_in_rect : (n, 3) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
        obtain ⟨d_n3, hd_n3_mem, hd_n3_cov⟩ := T.cell_covered (n, 3) hn3_in_rect
        have hd_n3_in_rect := T.dominos_in_rect d_n3 hd_n3_mem
        have h_n3_opts := domino_at_n3_options n d_n3 hd_n3_in_rect hd_n3_cov
        have hd_n3_cells : d_n3.cells = {(n, 2), (n, 3)} := by
          rcases h_n3_opts with h_left | h_right
          · exfalso
            rcases Nat.lt_or_ge n 4 with hn_lt4 | hn_ge4
            · have hn2 : n = 2 := by obtain ⟨k, hk⟩ := hn_even; omega
              obtain ⟨d_lw, hd_lw_mem, hd_lw_vert, hd_lw_col, hd_lw_rows⟩ := htop
              have hd_lw_c2_col : d_lw.cell2.1 = 1 := by rw [← hd_lw_vert, hd_lw_col]
              have h_13_in_lw : (1, 3) ∈ d_lw.cells := by
                simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
                obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hd_lw_rows
                · right; exact Prod.ext hd_lw_c2_col.symm h2.symm
                · left; exact Prod.ext hd_lw_col.symm h1.symm
              have h_n1_3 : (n - 1, 3) = (1, 3) := by simp [hn2]
              have h_13_in_n3 : (1, 3) ∈ d_n3.cells := by rw [h_left, h_n1_3]; simp
              by_cases heq : d_lw = d_n3
              · have hd_lw_cells : d_lw.cells = {(1, 2), (1, 3)} := by
                  simp only [Domino.cells]
                  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hd_lw_rows
                  · have hc1 : d_lw.cell1 = (1, 2) := Prod.ext hd_lw_col h1
                    have hc2 : d_lw.cell2 = (1, 3) := Prod.ext hd_lw_c2_col h2
                    simp [hc1, hc2]
                  · have hc1 : d_lw.cell1 = (1, 3) := Prod.ext hd_lw_col h1
                    have hc2 : d_lw.cell2 = (1, 2) := Prod.ext hd_lw_c2_col h2
                    simp [hc1, hc2, Finset.pair_comm]
                rw [heq, h_left, h_n1_3] at hd_lw_cells
                simp only [hn2] at hd_lw_cells
                have : (2, 3) ∈ ({(1, 3), (2, 3)} : Finset Cell) := by simp
                rw [hd_lw_cells] at this; simp at this
              · have h_disj := T.pairwise_disjoint d_lw hd_lw_mem d_n3 hd_n3_mem heq
                rw [Finset.disjoint_iff_ne] at h_disj
                exact h_disj (1, 3) h_13_in_lw (1, 3) h_13_in_n3 rfl
            · have hi_pos : n / 2 - 2 + 1 ≥ 1 := by omega
              have hi_lt : n / 2 - 2 + 1 < n / 2 := by omega
              obtain ⟨_, _, ⟨d_top, hd_top_mem, hd_top_cells⟩⟩ :=
                claim1_basement_middle_top n T hfree htop (n / 2 - 2 + 1) hi_pos hi_lt
              have h_top_c1 : 2 * (n / 2 - 2 + 1) = n - 2 := by obtain ⟨k, hk⟩ := hn_even; omega
              have h_top_c2 : 2 * (n / 2 - 2 + 1) + 1 = n - 1 := by obtain ⟨k, hk⟩ := hn_even; omega
              have hd_top_cells' : d_top.cells = {(n - 2, 3), (n - 1, 3)} := by
                rw [hd_top_cells, h_top_c2, h_top_c1]
              have h_n1_3_in_top : (n - 1, 3) ∈ d_top.cells := by rw [hd_top_cells']; simp
              have h_n1_3_in_n3 : (n - 1, 3) ∈ d_n3.cells := by rw [h_left]; simp
              by_cases heq : d_top = d_n3
              · rw [heq, h_left] at hd_top_cells'
                have h_n2 : (n - 2, 3) ∈ ({(n - 1, 3), (n, 3)} : Finset Cell) := by
                  rw [hd_top_cells']; simp
                simp only [Finset.mem_insert, Finset.mem_singleton] at h_n2
                rcases h_n2 with h1 | h2
                · simp only [Prod.mk.injEq] at h1; obtain ⟨h1a, _⟩ := h1; omega
                · simp only [Prod.mk.injEq] at h2; obtain ⟨h2a, _⟩ := h2; omega
              · have h_disj := T.pairwise_disjoint d_top hd_top_mem d_n3 hd_n3_mem heq
                rw [Finset.disjoint_iff_ne] at h_disj
                exact h_disj (n - 1, 3) h_n1_3_in_top (n - 1, 3) h_n1_3_in_n3 rfl
          · exact h_right
        have h_n2_in_n3 : (n, 2) ∈ d_n3.cells := by rw [hd_n3_cells]; simp
        have hn1_in_rect : (n, 1) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
        obtain ⟨d_n1, hd_n1_mem, hd_n1_cov⟩ := T.cell_covered (n, 1) hn1_in_rect
        have hd_n1_in_rect := T.dominos_in_rect d_n1 hd_n1_mem
        have h_n1_opts := domino_at_n1_options n d_n1 hd_n1_in_rect hd_n1_cov
        have hd_n1_cells : d_n1.cells = {(n - 1, 1), (n, 1)} := by
          rcases h_n1_opts with h_left | h_right
          · exact h_left
          · exfalso
            have h_n2_in_n1 : (n, 2) ∈ d_n1.cells := by rw [h_right]; simp
            by_cases heq : d_n1 = d_n3
            · rw [heq, hd_n3_cells] at h_right
              have h_n1 : (n, 1) ∈ ({(n, 2), (n, 3)} : Finset Cell) := by rw [h_right]; simp
              simp at h_n1
            · have h_disj := T.pairwise_disjoint d_n1 hd_n1_mem d_n3 hd_n3_mem heq
              rw [Finset.disjoint_iff_ne] at h_disj
              exact h_disj (n, 2) h_n2_in_n1 (n, 2) h_n2_in_n3 rfl
        use d_n1, hd_n1_mem
        rw [← hd_cells]
        simp only [Domino.cells, hd_c1, hd_c2]
        rw [show ({d_n1.cell1, d_n1.cell2} : Finset Cell) = d_n1.cells from rfl, hd_n1_cells]
    · -- d = leftWall
      obtain ⟨d', hd'_mem, hd'_vert, hd'_col, hd'_rows⟩ := htop
      use d', hd'_mem
      rw [← hd_cells]
      simp only [Domino.cells, leftWall] at hd ⊢
      have hcol2 : d'.cell2.1 = 1 := by rw [← hd'_vert, hd'_col]
      obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hd'_rows
      · have hc1 : d'.cell1 = (1, 2) := Prod.ext hd'_col h1
        have hc2 : d'.cell2 = (1, 3) := Prod.ext hcol2 h2
        simp only [hd, hc1, hc2]
      · have hc1 : d'.cell1 = (1, 3) := Prod.ext hd'_col h1
        have hc2 : d'.cell2 = (1, 2) := Prod.ext hcol2 h2
        simp only [hd, hc1, hc2, Finset.pair_comm]
    · -- d = rightWall n
      simp only [rightWall] at hd
      have hd_c1 : d.cell1 = (n, 2) := by simp [hd]
      have hd_c2 : d.cell2 = (n, 3) := by simp [hd]
      have hn3_in_rect : (n, 3) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
      obtain ⟨d_n3, hd_n3_mem, hd_n3_cov⟩ := T.cell_covered (n, 3) hn3_in_rect
      have hd_n3_in_rect := T.dominos_in_rect d_n3 hd_n3_mem
      have h_n3_opts := domino_at_n3_options n d_n3 hd_n3_in_rect hd_n3_cov
      have hd_n3_cells : d_n3.cells = {(n, 2), (n, 3)} := by
        rcases h_n3_opts with h_left | h_right
        · exfalso
          rcases Nat.lt_or_ge n 4 with hn_lt4 | hn_ge4
          · have hn2 : n = 2 := by obtain ⟨k, hk⟩ := hn_even; omega
            obtain ⟨d_lw, hd_lw_mem, hd_lw_vert, hd_lw_col, hd_lw_rows⟩ := htop
            have hd_lw_c2_col : d_lw.cell2.1 = 1 := by rw [← hd_lw_vert, hd_lw_col]
            have h_13_in_lw : (1, 3) ∈ d_lw.cells := by
              simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hd_lw_rows
              · right; exact Prod.ext hd_lw_c2_col.symm h2.symm
              · left; exact Prod.ext hd_lw_col.symm h1.symm
            have h_n1_3 : (n - 1, 3) = (1, 3) := by simp [hn2]
            have h_13_in_n3 : (1, 3) ∈ d_n3.cells := by rw [h_left, h_n1_3]; simp
            by_cases heq : d_lw = d_n3
            · have hd_lw_cells : d_lw.cells = {(1, 2), (1, 3)} := by
                simp only [Domino.cells]
                obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hd_lw_rows
                · have hc1 : d_lw.cell1 = (1, 2) := Prod.ext hd_lw_col h1
                  have hc2 : d_lw.cell2 = (1, 3) := Prod.ext hd_lw_c2_col h2
                  simp [hc1, hc2]
                · have hc1 : d_lw.cell1 = (1, 3) := Prod.ext hd_lw_col h1
                  have hc2 : d_lw.cell2 = (1, 2) := Prod.ext hd_lw_c2_col h2
                  simp [hc1, hc2, Finset.pair_comm]
              rw [heq, h_left, h_n1_3] at hd_lw_cells
              simp only [hn2] at hd_lw_cells
              have : (2, 3) ∈ ({(1, 3), (2, 3)} : Finset Cell) := by simp
              rw [hd_lw_cells] at this; simp at this
            · have h_disj := T.pairwise_disjoint d_lw hd_lw_mem d_n3 hd_n3_mem heq
              rw [Finset.disjoint_iff_ne] at h_disj
              exact h_disj (1, 3) h_13_in_lw (1, 3) h_13_in_n3 rfl
          · have hi_pos : n / 2 - 2 + 1 ≥ 1 := by omega
            have hi_lt : n / 2 - 2 + 1 < n / 2 := by omega
            obtain ⟨_, _, ⟨d_top, hd_top_mem, hd_top_cells⟩⟩ :=
              claim1_basement_middle_top n T hfree htop (n / 2 - 2 + 1) hi_pos hi_lt
            have h_top_c1 : 2 * (n / 2 - 2 + 1) = n - 2 := by obtain ⟨k, hk⟩ := hn_even; omega
            have h_top_c2 : 2 * (n / 2 - 2 + 1) + 1 = n - 1 := by obtain ⟨k, hk⟩ := hn_even; omega
            have hd_top_cells' : d_top.cells = {(n - 2, 3), (n - 1, 3)} := by
              rw [hd_top_cells, h_top_c2, h_top_c1]
            have h_n1_3_in_top : (n - 1, 3) ∈ d_top.cells := by rw [hd_top_cells']; simp
            have h_n1_3_in_n3 : (n - 1, 3) ∈ d_n3.cells := by rw [h_left]; simp
            by_cases heq : d_top = d_n3
            · rw [heq, h_left] at hd_top_cells'
              have h_n2 : (n - 2, 3) ∈ ({(n - 1, 3), (n, 3)} : Finset Cell) := by
                rw [hd_top_cells']; simp
              simp only [Finset.mem_insert, Finset.mem_singleton] at h_n2
              rcases h_n2 with h1 | h2
              · simp only [Prod.mk.injEq] at h1; obtain ⟨h1a, _⟩ := h1; omega
              · simp only [Prod.mk.injEq] at h2; obtain ⟨h2a, _⟩ := h2; omega
            · have h_disj := T.pairwise_disjoint d_top hd_top_mem d_n3 hd_n3_mem heq
              rw [Finset.disjoint_iff_ne] at h_disj
              exact h_disj (n - 1, 3) h_n1_3_in_top (n - 1, 3) h_n1_3_in_n3 rfl
        · exact h_right
      use d_n3, hd_n3_mem
      rw [← hd_cells]
      simp only [Domino.cells, hd_c1, hd_c2]
      rw [show ({d_n3.cell1, d_n3.cell2} : Finset Cell) = d_n3.cells from rfl, hd_n3_cells]
    · -- d ∈ middleDominos n
      simp only [middleDominos, Finset.mem_map, Finset.mem_range] at hd
      obtain ⟨j, hj_lt, hd_eq⟩ := hd
      have hd_cell1 : d.cell1 = (2 * j + 2, 2) := by
        simp only [← Function.Embedding.toFun_eq_coe] at hd_eq; rw [← hd_eq]
      have hd_cell2 : d.cell2 = (2 * j + 3, 2) := by
        simp only [← Function.Embedding.toFun_eq_coe] at hd_eq; rw [← hd_eq]
      have hi_pos : j + 1 ≥ 1 := by omega
      have hi_lt : j + 1 < n / 2 := by omega
      obtain ⟨_, ⟨d', hd'_mem, hd'_cells⟩, _⟩ :=
        claim1_basement_middle_top n T hfree htop (j + 1) hi_pos hi_lt
      use d', hd'_mem
      rw [← hd_cells]
      simp only [Domino.cells, hd_cell1, hd_cell2]
      -- Need to show: {(2 * j + 2, 2), (2 * j + 3, 2)} = {(2 * (j + 1), 2), (2 * (j + 1) + 1, 2)}
      convert hd'_cells using 2; simp [Domino.cells]
    · -- d ∈ topDominos n
      simp only [topDominos, Finset.mem_map, Finset.mem_range] at hd
      obtain ⟨j, hj_lt, hd_eq⟩ := hd
      have hd_cell1 : d.cell1 = (2 * j + 2, 3) := by
        simp only [← Function.Embedding.toFun_eq_coe] at hd_eq; rw [← hd_eq]
      have hd_cell2 : d.cell2 = (2 * j + 3, 3) := by
        simp only [← Function.Embedding.toFun_eq_coe] at hd_eq; rw [← hd_eq]
      have hi_pos : j + 1 ≥ 1 := by omega
      have hi_lt : j + 1 < n / 2 := by omega
      obtain ⟨_, _, ⟨d', hd'_mem, hd'_cells⟩⟩ :=
        claim1_basement_middle_top n T hfree htop (j + 1) hi_pos hi_lt
      use d', hd'_mem
      rw [← hd_cells]
      simp only [Domino.cells, hd_cell1, hd_cell2]
      -- Need to show: {(2 * j + 2, 3), (2 * j + 3, 3)} = {(2 * (j + 1), 3), (2 * (j + 1) + 1, 3)}
      convert hd'_cells using 2; simp [Domino.cells]
  -- Now use cardinality to show equality
  have h_image_card_eq : (T.dominos.image Domino.cells).card =
      ((TilingA n hn_even hn_ge).dominos.image Domino.cells).card := by
    have h1 : (T.dominos.image Domino.cells).card = T.dominos.card := by
      rw [Finset.card_image_of_injOn]
      exact h_cells_inj_T
    have h2 : ((TilingA n hn_even hn_ge).dominos.image Domino.cells).card =
        (TilingA n hn_even hn_ge).dominos.card := by
      rw [Finset.card_image_of_injOn]
      exact h_cells_inj_A
    omega
  -- By subset and equal cardinality, the sets are equal
  exact (Finset.eq_of_subset_of_card_le h_backward (by omega)).symm


-- created on 2026-10-20
