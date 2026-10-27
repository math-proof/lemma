import Mathlib
import Instance.Combinatorics.Tiling.DominoTilings.Part2
open Finset BigOperators


namespace DominoTilings

namespace DominoTiling

variable {n m : ℕ}


def isFaultfree (T : DominoTiling n m) : Prop :=
  ∀ k : ℕ, k ≥ 1 → k < n → ¬T.hasFaultAt k


def hasTopVerticalInCol (T : DominoTiling n m) (c : ℕ) : Prop :=
  ∃ d ∈ T.dominos, d.isVertical ∧ d.cell1.1 = c ∧
    ((d.cell1.2 = m - 1 ∧ d.cell2.2 = m) ∨ (d.cell1.2 = m ∧ d.cell2.2 = m - 1))


def hasBottomVerticalInCol (T : DominoTiling n m) (c : ℕ) : Prop :=
  ∃ d ∈ T.dominos, d.isVertical ∧ d.cell1.1 = c ∧
    ((d.cell1.2 = 1 ∧ d.cell2.2 = 2) ∨ (d.cell1.2 = 2 ∧ d.cell2.2 = 1))


def hasVerticalInCol (T : DominoTiling n m) (c : ℕ) : Prop :=
  ∃ d ∈ T.dominos, d.isVertical ∧ d.cell1.1 = c


def TilingEquiv (T₁ T₂ : DominoTiling n m) : Prop :=
  T₁.dominos.image Domino.cells = T₂.dominos.image Domino.cells


def prependVertical (T : DominoTiling n 2) : DominoTiling (n + 1) 2 where
  dominos := insert vertical_1_1 (T.dominos.image (fun d => d.shiftNat 1))
  dominos_in_rect := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_image] at hd
    rcases hd with rfl | ⟨d', hd', rfl⟩
    · -- Case: d = vertical_1_1
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · simp [mem_Rectangle]
      · simp [mem_Rectangle]
    · -- Case: d is a shifted domino
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · -- c = d'.shiftNat 1.cell1
        have hd'_in := T.dominos_in_rect d' hd'
        have hd'_c1 : d'.cell1 ∈ d'.cells := Finset.mem_insert_self _ _
        have h := hd'_in hd'_c1
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNat_cell1]
        omega
      · -- c = d'.shiftNat 1.cell2
        have hd'_in := T.dominos_in_rect d' hd'
        have hd'_c2 : d'.cell2 ∈ d'.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have h := hd'_in hd'_c2
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNat_cell2]
        omega
  covers_all := by
    ext c
    constructor
    · -- Forward: c in union → c in Rectangle (n+1) 2
      intro hc
      simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image] at hc
      rcases hc with ⟨d, hd, hc_in_d⟩
      rcases hd with rfl | ⟨d', hd', rfl⟩
      · -- d = vertical_1_1
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · simp [mem_Rectangle]
        · simp [mem_Rectangle]
      · -- d is shifted
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · have hd'_in := T.dominos_in_rect d' hd'
          have hd'_c1 : d'.cell1 ∈ d'.cells := Finset.mem_insert_self _ _
          have h := hd'_in hd'_c1
          rw [mem_Rectangle] at h ⊢
          simp only [Domino.shiftNat_cell1]
          omega
        · have hd'_in := T.dominos_in_rect d' hd'
          have hd'_c2 : d'.cell2 ∈ d'.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          have h := hd'_in hd'_c2
          rw [mem_Rectangle] at h ⊢
          simp only [Domino.shiftNat_cell2]
          omega
    · -- Backward: c in Rectangle (n+1) 2 → c in union
      intro hc
      rw [mem_Rectangle] at hc
      simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image]
      -- Case split on column of c
      by_cases hcol : c.1 = 1
      · -- Column 1: covered by vertical_1_1
        use vertical_1_1
        constructor
        · left; rfl
        · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
          -- c.2 ∈ {1, 2} since c ∈ Rectangle (n+1) 2
          have hrow_ge := hc.2.2.1
          have hrow_le := hc.2.2.2
          rcases Nat.eq_or_lt_of_le hrow_ge with hr1 | hr_gt
          · left; ext <;> simp [hcol, hr1.symm]
          · have hr2 : c.2 = 2 := by omega
            right; ext <;> simp [hcol, hr2]
      · -- Column > 1: covered by shifted domino
        have hcol_ge2 : c.1 ≥ 2 := by omega
        -- Find the original cell (c.1 - 1, c.2) in Rectangle n 2
        have hc_orig : (c.1 - 1, c.2) ∈ Rectangle n 2 := by
          rw [mem_Rectangle]
          omega
        -- This cell is covered by some domino in T
        rw [← T.covers_all] at hc_orig
        simp only [Finset.mem_biUnion] at hc_orig
        rcases hc_orig with ⟨d', hd', hc_in_d'⟩
        -- The shifted domino covers c
        use d'.shiftNat 1
        constructor
        · right; exact ⟨d', hd', rfl⟩
        · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d' ⊢
          rcases hc_in_d' with heq1 | heq2
          · left
            simp only [Domino.shiftNat_cell1]
            have hcol_eq := congrArg Prod.fst heq1
            have hrow_eq := congrArg Prod.snd heq1
            simp at hcol_eq hrow_eq
            ext
            · simp; omega
            · simp; exact hrow_eq
          · right
            simp only [Domino.shiftNat_cell2]
            have hcol_eq := congrArg Prod.fst heq2
            have hrow_eq := congrArg Prod.snd heq2
            simp at hcol_eq hrow_eq
            ext
            · simp; omega
            · simp; exact hrow_eq
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Finset.mem_insert, Finset.mem_image] at hd1 hd2
    rcases hd1 with rfl | ⟨d1', hd1', rfl⟩
    · -- d1 = vertical_1_1
      rcases hd2 with rfl | ⟨d2', hd2', rfl⟩
      · -- d2 = vertical_1_1 - contradiction
        exact absurd rfl hne
      · -- d2 is shifted
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        -- c1 ∈ vertical_1_1.cells has column 1
        -- c2 ∈ (d2'.shiftNat 1).cells has column ≥ 2
        have hcol := (domino_cells_col_ge_one T d2' hd2')
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        all_goals
          simp only [vertical_1_1_cell1, vertical_1_1_cell2, Domino.shiftNat_cell1,
                     Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          omega
    · -- d1 is shifted
      rcases hd2 with rfl | ⟨d2', hd2', rfl⟩
      · -- d2 = vertical_1_1
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        have hcol := (domino_cells_col_ge_one T d1' hd1')
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        all_goals
          simp only [vertical_1_1_cell1, vertical_1_1_cell2, Domino.shiftNat_cell1,
                     Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          omega
      · -- Both are shifted
        -- Need: d1' ≠ d2' (since shifting is injective and d1 ≠ d2)
        have hne' : d1' ≠ d2' := by
          intro heq'
          apply hne
          rw [heq']
        have hdisj := T.pairwise_disjoint d1' hd1' d2' hd2' hne'
        rw [Finset.disjoint_iff_ne] at hdisj ⊢
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        -- Extract the original cells
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        · -- cell1 vs cell1
          simp only [Domino.shiftNat_cell1, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell1 = d2'.cell1 := by ext <;> omega
          exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell1 (Finset.mem_insert_self _ _) heq_orig
        · -- cell1 vs cell2
          simp only [Domino.shiftNat_cell1, Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell1 = d2'.cell2 := by ext <;> omega
          exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig
        · -- cell2 vs cell1
          simp only [Domino.shiftNat_cell1, Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell2 = d2'.cell1 := by ext <;> omega
          exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell1 (Finset.mem_insert_self _ _) heq_orig
        · -- cell2 vs cell2
          simp only [Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell2 = d2'.cell2 := by ext <;> omega
          exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig


def prependHorizontalPair (T : DominoTiling n 2) : DominoTiling (n + 2) 2 where
  dominos := insert horizontal_1_1 (insert horizontal_1_2 (T.dominos.image (fun d => d.shiftNat 2)))
  dominos_in_rect := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_image] at hd
    rcases hd with rfl | rfl | ⟨d', hd', rfl⟩
    · -- Case: d = horizontal_1_1
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · simp [mem_Rectangle]
      · simp [mem_Rectangle]
    · -- Case: d = horizontal_1_2
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · simp [mem_Rectangle]
      · simp [mem_Rectangle]
    · -- Case: d is a shifted domino
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · -- c = d'.shiftNat 2.cell1
        have hd'_in := T.dominos_in_rect d' hd'
        have hd'_c1 : d'.cell1 ∈ d'.cells := Finset.mem_insert_self _ _
        have h := hd'_in hd'_c1
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNat_cell1]
        omega
      · -- c = d'.shiftNat 2.cell2
        have hd'_in := T.dominos_in_rect d' hd'
        have hd'_c2 : d'.cell2 ∈ d'.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have h := hd'_in hd'_c2
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNat_cell2]
        omega
  covers_all := by
    ext c
    constructor
    · -- Forward: c in union → c in Rectangle (n+2) 2
      intro hc
      simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image] at hc
      rcases hc with ⟨d, hd, hc_in_d⟩
      rcases hd with rfl | rfl | ⟨d', hd', rfl⟩
      · -- d = horizontal_1_1
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · simp [mem_Rectangle]
        · simp [mem_Rectangle]
      · -- d = horizontal_1_2
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · simp [mem_Rectangle]
        · simp [mem_Rectangle]
      · -- d is shifted
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · have hd'_in := T.dominos_in_rect d' hd'
          have hd'_c1 : d'.cell1 ∈ d'.cells := Finset.mem_insert_self _ _
          have h := hd'_in hd'_c1
          rw [mem_Rectangle] at h ⊢
          simp only [Domino.shiftNat_cell1]
          omega
        · have hd'_in := T.dominos_in_rect d' hd'
          have hd'_c2 : d'.cell2 ∈ d'.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          have h := hd'_in hd'_c2
          rw [mem_Rectangle] at h ⊢
          simp only [Domino.shiftNat_cell2]
          omega
    · -- Backward: c in Rectangle (n+2) 2 → c in union
      intro hc
      rw [mem_Rectangle] at hc
      simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image]
      -- Case split on column of c
      rcases Nat.lt_trichotomy c.1 2 with hcol_lt | hcol_eq | hcol_gt
      · -- Column 1: covered by horizontal_1_1 or horizontal_1_2
        have hcol1 : c.1 = 1 := by omega
        have hrow_ge := hc.2.2.1
        have hrow_le := hc.2.2.2
        rcases Nat.eq_or_lt_of_le hrow_ge with hr1 | hr_gt
        · -- Row 1: horizontal_1_1
          use horizontal_1_1
          constructor
          · left; rfl
          · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            left; ext <;> simp [hcol1, hr1.symm]
        · -- Row 2: horizontal_1_2
          have hr2 : c.2 = 2 := by omega
          use horizontal_1_2
          constructor
          · right; left; rfl
          · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            left; ext <;> simp [hcol1, hr2]
      · -- Column 2: covered by horizontal_1_1 or horizontal_1_2
        have hrow_ge := hc.2.2.1
        have hrow_le := hc.2.2.2
        rcases Nat.eq_or_lt_of_le hrow_ge with hr1 | hr_gt
        · -- Row 1: horizontal_1_1
          use horizontal_1_1
          constructor
          · left; rfl
          · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            right; ext <;> simp [hcol_eq, hr1.symm]
        · -- Row 2: horizontal_1_2
          have hr2 : c.2 = 2 := by omega
          use horizontal_1_2
          constructor
          · right; left; rfl
          · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            right; ext <;> simp [hcol_eq, hr2]
      · -- Column > 2: covered by shifted domino
        have hcol_ge3 : c.1 ≥ 3 := by omega
        -- Find the original cell (c.1 - 2, c.2) in Rectangle n 2
        have hc_orig : (c.1 - 2, c.2) ∈ Rectangle n 2 := by
          rw [mem_Rectangle]
          omega
        -- This cell is covered by some domino in T
        rw [← T.covers_all] at hc_orig
        simp only [Finset.mem_biUnion] at hc_orig
        rcases hc_orig with ⟨d', hd', hc_in_d'⟩
        -- The shifted domino covers c
        use d'.shiftNat 2
        constructor
        · right; right; exact ⟨d', hd', rfl⟩
        · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d' ⊢
          rcases hc_in_d' with heq1 | heq2
          · left
            simp only [Domino.shiftNat_cell1]
            have hcol_eq' := congrArg Prod.fst heq1
            have hrow_eq := congrArg Prod.snd heq1
            simp at hcol_eq' hrow_eq
            ext
            · simp; omega
            · simp; exact hrow_eq
          · right
            simp only [Domino.shiftNat_cell2]
            have hcol_eq' := congrArg Prod.fst heq2
            have hrow_eq := congrArg Prod.snd heq2
            simp at hcol_eq' hrow_eq
            ext
            · simp; omega
            · simp; exact hrow_eq
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Finset.mem_insert, Finset.mem_image] at hd1 hd2
    rcases hd1 with rfl | rfl | ⟨d1', hd1', rfl⟩
    · -- d1 = horizontal_1_1
      rcases hd2 with rfl | rfl | ⟨d2', hd2', rfl⟩
      · -- d2 = horizontal_1_1 - contradiction
        exact absurd rfl hne
      · -- d2 = horizontal_1_2
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
          simp only [horizontal_1_1_cell1, horizontal_1_1_cell2, horizontal_1_2_cell1,
                     horizontal_1_2_cell2, Prod.mk.injEq] at heq <;>
          omega
      · -- d2 is shifted
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        have hcol := (domino_cells_col_ge_one T d2' hd2')
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        all_goals
          simp only [horizontal_1_1_cell1, horizontal_1_1_cell2, Domino.shiftNat_cell1,
                     Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          omega
    · -- d1 = horizontal_1_2
      rcases hd2 with rfl | rfl | ⟨d2', hd2', rfl⟩
      · -- d2 = horizontal_1_1
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
          simp only [horizontal_1_1_cell1, horizontal_1_1_cell2, horizontal_1_2_cell1,
                     horizontal_1_2_cell2, Prod.mk.injEq] at heq <;>
          omega
      · -- d2 = horizontal_1_2 - contradiction
        exact absurd rfl hne
      · -- d2 is shifted
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        have hcol := (domino_cells_col_ge_one T d2' hd2')
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        all_goals
          simp only [horizontal_1_2_cell1, horizontal_1_2_cell2, Domino.shiftNat_cell1,
                     Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          omega
    · -- d1 is shifted
      rcases hd2 with rfl | rfl | ⟨d2', hd2', rfl⟩
      · -- d2 = horizontal_1_1
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        have hcol := (domino_cells_col_ge_one T d1' hd1')
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        all_goals
          simp only [horizontal_1_1_cell1, horizontal_1_1_cell2, Domino.shiftNat_cell1,
                     Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          omega
      · -- d2 = horizontal_1_2
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        have hcol := (domino_cells_col_ge_one T d1' hd1')
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        all_goals
          simp only [horizontal_1_2_cell1, horizontal_1_2_cell2, Domino.shiftNat_cell1,
                     Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          omega
      · -- Both are shifted
        have hne' : d1' ≠ d2' := by
          intro heq'
          apply hne
          rw [heq']
        have hdisj := T.pairwise_disjoint d1' hd1' d2' hd2' hne'
        rw [Finset.disjoint_iff_ne] at hdisj ⊢
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        · -- cell1 vs cell1
          simp only [Domino.shiftNat_cell1, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell1 = d2'.cell1 := by ext <;> omega
          exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell1 (Finset.mem_insert_self _ _) heq_orig
        · -- cell1 vs cell2
          simp only [Domino.shiftNat_cell1, Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell1 = d2'.cell2 := by ext <;> omega
          exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig
        · -- cell2 vs cell1
          simp only [Domino.shiftNat_cell1, Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell2 = d2'.cell1 := by ext <;> omega
          exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell1 (Finset.mem_insert_self _ _) heq_orig
        · -- cell2 vs cell2
          simp only [Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell2 = d2'.cell2 := by ext <;> omega
          exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig


end DominoTiling
end DominoTilings
