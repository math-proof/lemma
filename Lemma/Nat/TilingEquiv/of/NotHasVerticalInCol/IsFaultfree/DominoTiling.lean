import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings
import Lemma.Nat.IffIn_RectangleGe1AndGe_1AndGe21AndGe_2
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
  (T : DominoTiling 2 3)
  (hno_vert : ¬T.hasVerticalInCol 1)
  (_ : T.isFaultfree) :
-- imply
  DominoTiling.TilingEquiv T TilingC := by
-- proof
  -- Strategy: Show every domino in T is horizontal, then the cells image matches TilingC -- Key insight: In a 2×3 rectangle with no vertical in column 1, all dominos must be horizontal -- because any vertical domino would have to be in column 1 or 2, and column 2 would force -- a horizontal domino to overlap with it.
  -- First, show every domino in T is horizontal
  have h_all_horiz : ∀ d ∈ T.dominos, d.isHorizontal := by
    intro d hd
    have h_in_rect := T.dominos_in_rect d hd -- A domino is either vertical or horizontal
    obtain ⟨hcol, _⟩ | ⟨hrow, _⟩ := d.adjacent
    ·
      -- Vertical case: d.cell1.1 = d.cell2.1
      exfalso -- d is vertical, so both cells are in the same column
      have hv : d.isVertical := hcol -- Get column bounds from rectangle membership
      have h1 : d.cell1 ∈ Rectangle 2 3 := h_in_rect (Finset.mem_insert_self _ _)
      rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at h1 -- Column must be 1 or 2
      have hcol_bounds : d.cell1.1 = 1 ∨ d.cell1.1 = 2 := by omega
      obtain hc | hc := hcol_bounds
      ·
        -- Column 1: contradicts hno_vert
        apply hno_vert
        exact ⟨d, hd, hv, hc⟩
      ·
        -- Column 2: Show this leads to contradiction
        -- d covers (2, r) and (2, r±1) for some r
        -- Cell (1, r) must be covered by some domino d' in T
        -- d' can't be vertical in column 1 (hypothesis)
        -- d' must be horizontal, covering (1, r) and (2, r)
        -- But (2, r) is already covered by d - contradiction with pairwise disjoint!
        have h2 : d.cell2 ∈ Rectangle 2 3 :=
          h_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at h2 -- d.cell1 = (2, r) for some r ∈ {1, 2, 3}
        have hr_bounds : d.cell1.2 ≥ 1 ∧ d.cell1.2 ≤ 3 := ⟨h1.2.2.1, h1.2.2.2⟩ -- Cell (1, d.cell1.2) is in the rectangle and must be covered
        have h_cell_in_rect : (1, d.cell1.2) ∈ Rectangle 2 3 := by
          rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2]; omega -- Find the domino d' that covers (1, d.cell1.2)
        have h_covered := T.covers_all
        rw [Finset.ext_iff] at h_covered
        have h_in_union : (1, d.cell1.2) ∈ T.dominos.biUnion Domino.cells := by
          rwa [h_covered]
        rw [Finset.mem_biUnion] at h_in_union
        obtain ⟨d', hd'_mem, hd'_covers⟩ := h_in_union -- d' covers (1, d.cell1.2), so d'.cell1 = (1, r) or d'.cell2 = (1, r) where r = d.cell1.2
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd'_covers -- d' is either vertical or horizontal
        obtain ⟨hcol', _⟩ | ⟨hrow', hcol_adj'⟩ := d'.adjacent
        ·
          -- d' is vertical
          -- d'.cell1.1 = d'.cell2.1
          -- Since d' covers (1, r), we have d'.cell1.1 = 1 or d'.cell2.1 = 1
          -- So d' is vertical in column 1 - contradiction!
          obtain hc1 | hc2 := hd'_covers
          ·
            -- d'.cell1 = (1, d.cell1.2)
            have : d'.cell1.1 = 1 := by rw [← hc1]
            apply hno_vert
            exact ⟨d', hd'_mem, hcol', this⟩
          ·
            -- d'.cell2 = (1, d.cell1.2)
            have hc2_col : d'.cell2.1 = 1 := by rw [← hc2]
            have hc1_col : d'.cell1.1 = 1 := hcol'.symm ▸ hc2_col
            apply hno_vert
            exact ⟨d', hd'_mem, hcol', hc1_col⟩
        ·
          -- d' is horizontal: d'.cell1.2 = d'.cell2.2
          -- d' covers (1, r) and extends horizontally
          -- From adjacency, d'.cell1.1 + 1 = d'.cell2.1 or d'.cell2.1 + 1 = d'.cell1.1
          -- Combined with d' covering (1, r), d' must cover (1, r) and (2, r)
          -- But (2, r) = (2, d.cell1.2) is covered by d (since d.cell1 = (2, d.cell1.2))
          -- This contradicts pairwise disjoint!
          obtain hc1 | hc2 := hd'_covers
          ·
            -- d'.cell1 = (1, d.cell1.2)
            -- d'.cell2.2 = d'.cell1.2 = d.cell1.2
            have hd'1_row : d'.cell1.2 = d.cell1.2 := (congrArg Prod.snd hc1).symm
            have hd'_row : d'.cell2.2 = d.cell1.2 := hrow'.symm.trans hd'1_row -- d'.cell2.1 = 2 (from adjacency and bounds)
            have hd'_in_rect := T.dominos_in_rect d' hd'_mem
            have hd'2_in : d'.cell2 ∈ Rectangle 2 3 :=
              hd'_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
            rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at hd'2_in
            have hd'1_col : d'.cell1.1 = 1 := (congrArg Prod.fst hc1).symm
            obtain hadj | hadj := hcol_adj'
            ·
              -- d'.cell1.1 + 1 = d'.cell2.1
              have hd'2_col : d'.cell2.1 = 2 := by omega -- d'.cell2 = (2, d.cell1.2)
              have hd'2_eq : d'.cell2 = (2, d.cell1.2) := Prod.ext hd'2_col hd'_row -- d.cell1 = (2, d.cell1.2) (since d.cell1.1 = 2 from hc)
              have hd1_eq : d.cell1 = (2, d.cell1.2) := Prod.ext hc rfl -- d'.cell2 = d.cell1
              have h_overlap :
                d'.cell2 = d.cell1 := by rw [hd'2_eq, hd1_eq] -- d' ≠ d (d' covers column 1, d is in column 2)
              have hne : d' ≠ d := by
                intro heq; subst heq
                omega -- d' and d share cell d.cell1, contradicting pairwise disjoint
              have h_disj := T.pairwise_disjoint d' hd'_mem d hd hne
              rw [Finset.disjoint_iff_ne] at h_disj
              refine h_disj d.cell1 ?_ d.cell1 (Finset.mem_insert_self _ _) rfl
              ·
                simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
                right
                exact h_overlap.symm
            ·
              -- d'.cell2.1 + 1 = d'.cell1.1
              -- d'.cell1.1 = 1 (from hc1), so d'.cell2.1 = 0
              -- But d'.cell2 ∈ Rectangle 2 3, so d'.cell2.1 ≥ 1 - contradiction!
              omega
          ·
            -- d'.cell2 = (1, d.cell1.2)
            -- Similar argument
            have hd'2_row : d'.cell2.2 = d.cell1.2 := (congrArg Prod.snd hc2).symm
            have hd'_row : d'.cell1.2 = d.cell1.2 := hrow'.trans hd'2_row
            have hd'_in_rect := T.dominos_in_rect d' hd'_mem
            have hd'1_in : d'.cell1 ∈ Rectangle 2 3 :=
              hd'_in_rect (Finset.mem_insert_self _ _)
            rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at hd'1_in
            have hd'2_col : d'.cell2.1 = 1 := (congrArg Prod.fst hc2).symm
            obtain hadj | hadj := hcol_adj'
            ·
              -- d'.cell1.1 + 1 = d'.cell2.1
              -- d'.cell2.1 = 1 (from hc2), so d'.cell1.1 = 0
              -- But d'.cell1 ∈ Rectangle 2 3, so d'.cell1.1 ≥ 1 - contradiction!
              omega
            ·
              -- d'.cell2.1 + 1 = d'.cell1.1
              have hd'1_col : d'.cell1.1 = 2 := by omega
              have hd'1_eq : d'.cell1 = (2, d.cell1.2) := Prod.ext hd'1_col hd'_row
              have hd1_eq : d.cell1 = (2, d.cell1.2) := Prod.ext hc rfl
              have h_overlap : d'.cell1 = d.cell1 := by rw [hd'1_eq, hd1_eq]
              have hne : d' ≠ d := by
                intro heq; subst heq
                omega
              have h_disj := T.pairwise_disjoint d' hd'_mem d hd hne
              rw [Finset.disjoint_iff_ne] at h_disj
              refine h_disj d.cell1 ?_ d.cell1 (Finset.mem_insert_self _ _) rfl
              ·
                simp only [Domino.cells, Finset.mem_insert]
                left
                exact h_overlap.symm
    ·
      -- Horizontal case
      exact hrow
  -- Now show the cells images are equal
  -- Each horizontal domino in T covers {(1, r), (2, r)} for some row r ∈ {1, 2, 3}
  -- Since T partitions Rectangle 2 3, exactly one domino covers each row
  -- So T.dominos.image Domino.cells = {{(1,1), (2,1)}, {(1,2), (2,2)}, {(1,3), (2,3)}}
  -- This equals TilingC.dominos.image Domino.cells
  -- The detailed proof follows from h_all_horiz and the structure of Rectangle 2 3
  -- Helper: each horizontal domino d in Rectangle 2 3 has d.cells = {(1, r), (2, r)} for some r
  have h_cells_form :
    ∀ d ∈ T.dominos, ∃ r : ℕ, r ≥ 1 ∧ r ≤ 3 ∧ d.cells = {(1, r), (2, r)} := by
    intro d hd
    have h_horiz := h_all_horiz d hd
    have h_in_rect := T.dominos_in_rect d hd
    unfold Domino.isHorizontal at h_horiz
    have h1 := h_in_rect (Finset.mem_insert_self _ _)
    have h2 := h_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at h1 h2
    use d.cell1.2
    refine ⟨h1.2.2.1, h1.2.2.2, ?_⟩
    unfold Domino.cells
    obtain ⟨_, hadj⟩ | ⟨_, hadj⟩ := d.adjacent
    ·
      omega  -- vertical case contradicts h_horiz
    ·
      obtain hadj1 | hadj2 := hadj
      ·
        -- d.cell1.1 + 1 = d.cell2.1
        have hc1_col : d.cell1.1 = 1 := by omega
        have hc2_col : d.cell2.1 = 2 := by omega
        have hc1 : d.cell1 = (1, d.cell1.2) := Prod.ext hc1_col rfl
        have hc2 : d.cell2 = (2, d.cell1.2) := Prod.ext hc2_col h_horiz.symm
        rw [hc1, hc2]
      ·
        -- d.cell2.1 + 1 = d.cell1.1
        have hc2_col : d.cell2.1 = 1 := by omega
        have hc1_col : d.cell1.1 = 2 := by omega
        have hc1 : d.cell1 = (2, d.cell1.2) := Prod.ext hc1_col rfl
        have hc2 : d.cell2 = (1, d.cell1.2) := Prod.ext hc2_col h_horiz.symm
        rw [hc1, hc2, Finset.pair_comm]
  -- TilingEquiv means the cell images are equal
  unfold DominoTiling.TilingEquiv -- TilingC.dominos.image Domino.cells = {{(1,1), (2,1)}, {(1,2), (2,2)}, {(1,3), (2,3)}}
  have hC_image : TilingC.dominos.image Domino.cells =
      {{(1, 1), (2, 1)}, {(1, 2), (2, 2)}, {(1, 3), (2, 3)}} := by
    unfold TilingC
    decide
  rw [hC_image] -- Now show T.dominos.image Domino.cells = {{(1,1), (2,1)}, {(1,2), (2,2)}, {(1,3), (2,3)}}
  ext x
  constructor
  ·
    -- x ∈ T.dominos.image Domino.cells → x ∈ {{...}}
    intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, hd_mem, hd_eq⟩ := hx
    obtain ⟨r, hr_ge, hr_le, hr_cells⟩ := h_cells_form d hd_mem
    rw [← hd_eq, hr_cells]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases r <;> simp
  ·
    -- x ∈ {{...}} → x ∈ T.dominos.image Domino.cells
    intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    obtain rfl | rfl | rfl := hx
    ·
      -- x = {(1, 1), (2, 1)}
      -- Cell (1, 1) is covered by some domino d in T
      have h11_in : (1, 1) ∈ Rectangle 2 3 := by rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2]; omega
      have h11_covered : (1, 1) ∈ T.dominos.biUnion Domino.cells := by
        rwa [T.covers_all]
      rw [Finset.mem_biUnion] at h11_covered
      obtain ⟨d, hd_mem, hd_covers⟩ := h11_covered
      obtain ⟨r, _, _, hr_cells⟩ := h_cells_form d hd_mem
      rw [hr_cells] at hd_covers
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_covers
      obtain ⟨_, hr⟩ | ⟨_, hr⟩ := hd_covers <;> subst hr
      ·
        rw [Finset.mem_image]
        exact ⟨d, hd_mem, hr_cells⟩
      ·
        rw [Finset.mem_image]
        exact ⟨d, hd_mem, hr_cells⟩
    ·
      -- x = {(1, 2), (2, 2)}
      have h12_in : (1, 2) ∈ Rectangle 2 3 := by rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2]; omega
      have h12_covered : (1, 2) ∈ T.dominos.biUnion Domino.cells := by
        rwa [T.covers_all]
      rw [Finset.mem_biUnion] at h12_covered
      obtain ⟨d, hd_mem, hd_covers⟩ := h12_covered
      obtain ⟨r, _, _, hr_cells⟩ := h_cells_form d hd_mem
      rw [hr_cells] at hd_covers
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_covers
      obtain ⟨_, hr⟩ | ⟨_, hr⟩ := hd_covers <;> subst hr
      ·
        rw [Finset.mem_image]
        exact ⟨d, hd_mem, hr_cells⟩
      ·
        rw [Finset.mem_image]
        exact ⟨d, hd_mem, hr_cells⟩
    ·
      -- x = {(1, 3), (2, 3)}
      have h13_in : (1, 3) ∈ Rectangle 2 3 := by rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2]; omega
      have h13_covered : (1, 3) ∈ T.dominos.biUnion Domino.cells := by
        rwa [T.covers_all]
      rw [Finset.mem_biUnion] at h13_covered
      obtain ⟨d, hd_mem, hd_covers⟩ := h13_covered
      obtain ⟨r, _, _, hr_cells⟩ := h_cells_form d hd_mem
      rw [hr_cells] at hd_covers
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_covers
      obtain ⟨_, hr⟩ | ⟨_, hr⟩ := hd_covers <;> subst hr
      ·
        rw [Finset.mem_image]
        exact ⟨d, hd_mem, hr_cells⟩
      ·
        rw [Finset.mem_image]
        exact ⟨d, hd_mem, hr_cells⟩


-- created on 2026-10-20
