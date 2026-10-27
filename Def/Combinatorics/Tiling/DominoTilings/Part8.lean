import Mathlib
import Theorem.Combinatorics.Tiling.DominoTilings.Part5
open Finset BigOperators


namespace DominoTilings

namespace DominoTiling

variable {n m : ℕ}


def restrictAfterVertical (T : DominoTiling (n + 1) 2) (hv : vertical_1_1 ∈ T.dominos) :
    DominoTiling n 2 where
  dominos := (T.dominos.erase vertical_1_1).attach.image fun ⟨d, hd⟩ =>
    let hd' := Finset.mem_erase.mp hd
    let hcols := domino_col_ge_two_of_ne_vertical T hv d (Finset.mem_of_mem_erase hd) hd'.1
    d.shiftNeg 1 hcols.1 hcols.2
  dominos_in_rect := by
    intro d' hd'
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hd'
    obtain ⟨d, hd_erase, rfl⟩ := hd'
    have hd_ne := (Finset.mem_erase.mp hd_erase).1
    have hd_mem := Finset.mem_of_mem_erase hd_erase
    have hcols := domino_col_ge_two_of_ne_vertical T hv d hd_mem hd_ne
    intro c hc
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
    have hd_in_rect := T.dominos_in_rect d hd_mem
    rcases hc with rfl | rfl
    · have h := hd_in_rect (Finset.mem_insert_self _ _)
      rw [mem_Rectangle] at h ⊢
      simp only [Domino.shiftNeg_cell1]
      omega
    · have h := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rw [mem_Rectangle] at h ⊢
      simp only [Domino.shiftNeg_cell2]
      omega
  covers_all := by
    ext c
    constructor
    · intro hc
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists] at hc
      obtain ⟨d', ⟨d, hd_erase, rfl⟩, hc_in_d'⟩ := hc
      have hd_ne := (Finset.mem_erase.mp hd_erase).1
      have hd_mem := Finset.mem_of_mem_erase hd_erase
      have hcols := domino_col_ge_two_of_ne_vertical T hv d hd_mem hd_ne
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d'
      have hd_in_rect := T.dominos_in_rect d hd_mem
      rcases hc_in_d' with rfl | rfl
      · have h := hd_in_rect (Finset.mem_insert_self _ _)
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNeg_cell1]
        omega
      · have h := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNeg_cell2]
        omega
    · intro hc
      rw [mem_Rectangle] at hc
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists]
      -- The cell (c.1 + 1, c.2) is in Rectangle (n+1) 2 and is covered by some domino
      have hc_orig : (c.1 + 1, c.2) ∈ Rectangle (n + 1) 2 := by
        rw [mem_Rectangle]
        omega
      rw [← T.covers_all] at hc_orig
      simp only [Finset.mem_biUnion] at hc_orig
      obtain ⟨d, hd_mem, hc_in_d⟩ := hc_orig
      -- d cannot be vertical_1_1 since (c.1+1, c.2) has column ≥ 2
      have hd_ne : d ≠ vertical_1_1 := by
        intro heq
        subst heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton,
          vertical_1_1_cell1, vertical_1_1_cell2] at hc_in_d
        rcases hc_in_d with heq | heq
        · have := congrArg Prod.fst heq
          simp at this
          omega
        · have := congrArg Prod.fst heq
          simp at this
          omega
      have hd_erase : d ∈ T.dominos.erase vertical_1_1 := Finset.mem_erase.mpr ⟨hd_ne, hd_mem⟩
      have hcols := domino_col_ge_two_of_ne_vertical T hv d hd_mem hd_ne
      use d.shiftNeg 1 hcols.1 hcols.2
      constructor
      · use d, hd_erase
      · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d ⊢
        rcases hc_in_d with heq | heq
        · left
          simp only [Domino.shiftNeg_cell1]
          have hcol_eq := congrArg Prod.fst heq
          have hrow_eq := congrArg Prod.snd heq
          simp at hcol_eq hrow_eq
          ext <;> simp <;> omega
        · right
          simp only [Domino.shiftNeg_cell2]
          have hcol_eq := congrArg Prod.fst heq
          have hrow_eq := congrArg Prod.snd heq
          simp at hcol_eq hrow_eq
          ext <;> simp <;> omega
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hd1 hd2
    obtain ⟨d1', hd1'_erase, rfl⟩ := hd1
    obtain ⟨d2', hd2'_erase, rfl⟩ := hd2
    have hd1'_ne := (Finset.mem_erase.mp hd1'_erase).1
    have hd2'_ne := (Finset.mem_erase.mp hd2'_erase).1
    have hd1'_mem := Finset.mem_of_mem_erase hd1'_erase
    have hd2'_mem := Finset.mem_of_mem_erase hd2'_erase
    have hcols1 := domino_col_ge_two_of_ne_vertical T hv d1' hd1'_mem hd1'_ne
    have hcols2 := domino_col_ge_two_of_ne_vertical T hv d2' hd2'_mem hd2'_ne
    have hne' : d1' ≠ d2' := by
      intro heq
      apply hne
      subst heq
      rfl
    have hdisj := T.pairwise_disjoint d1' hd1'_mem d2' hd2'_mem hne'
    rw [Finset.disjoint_iff_ne] at hdisj ⊢
    intro c1 hc1 c2 hc2 heq
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
    rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
    · -- cell1 vs cell1
      simp only [Domino.shiftNeg_cell1, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell1 = d2'.cell1 := by ext <;> omega
      exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · -- cell1 vs cell2
      simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell1 = d2'.cell2 := by ext <;> omega
      exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig
    · -- cell2 vs cell1
      simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell2 = d2'.cell1 := by ext <;> omega
      exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · -- cell2 vs cell2
      simp only [Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell2 = d2'.cell2 := by ext <;> omega
      exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig


def restrictAfterHorizontalPair (T : DominoTiling (n + 2) 2)
    (hh1 : horizontal_1_1 ∈ T.dominos) (hh2 : horizontal_1_2 ∈ T.dominos) :
    DominoTiling n 2 where
  dominos := ((T.dominos.erase horizontal_1_1).erase horizontal_1_2).attach.image fun ⟨d, hd⟩ =>
    let hd' := Finset.mem_erase.mp hd
    let hd'' := Finset.mem_erase.mp (Finset.mem_of_mem_erase hd)
    let hcols := other_dominos_col_ge_3 T hh1 hh2 d (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd)) hd''.1 hd'.1
    d.shiftNeg 2 hcols.1 hcols.2
  dominos_in_rect := by
    intro d' hd'
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hd'
    obtain ⟨d, hd_erase, rfl⟩ := hd'
    have hd_erase2 := Finset.mem_of_mem_erase hd_erase
    have hd_ne2 := (Finset.mem_erase.mp hd_erase).1
    have hd_ne1 := (Finset.mem_erase.mp hd_erase2).1
    have hd_mem := Finset.mem_of_mem_erase hd_erase2
    have hcols := other_dominos_col_ge_3 T hh1 hh2 d hd_mem hd_ne1 hd_ne2
    intro c hc
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
    have hd_in_rect := T.dominos_in_rect d hd_mem
    rcases hc with rfl | rfl
    · have h := hd_in_rect (Finset.mem_insert_self _ _)
      rw [mem_Rectangle] at h ⊢
      simp only [Domino.shiftNeg_cell1]
      omega
    · have h := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rw [mem_Rectangle] at h ⊢
      simp only [Domino.shiftNeg_cell2]
      omega
  covers_all := by
    ext c
    constructor
    · intro hc
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists] at hc
      obtain ⟨d', ⟨d, hd_erase, rfl⟩, hc_in_d'⟩ := hc
      have hd_erase2 := Finset.mem_of_mem_erase hd_erase
      have hd_ne2 := (Finset.mem_erase.mp hd_erase).1
      have hd_ne1 := (Finset.mem_erase.mp hd_erase2).1
      have hd_mem := Finset.mem_of_mem_erase hd_erase2
      have hcols := other_dominos_col_ge_3 T hh1 hh2 d hd_mem hd_ne1 hd_ne2
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d'
      have hd_in_rect := T.dominos_in_rect d hd_mem
      rcases hc_in_d' with rfl | rfl
      · have h := hd_in_rect (Finset.mem_insert_self _ _)
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNeg_cell1]
        omega
      · have h := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNeg_cell2]
        omega
    · intro hc
      rw [mem_Rectangle] at hc
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists]
      -- The cell (c.1 + 2, c.2) is in Rectangle (n+2) 2 and is covered by some domino
      have hc_orig : (c.1 + 2, c.2) ∈ Rectangle (n + 2) 2 := by
        rw [mem_Rectangle]
        omega
      rw [← T.covers_all] at hc_orig
      simp only [Finset.mem_biUnion] at hc_orig
      obtain ⟨d, hd_mem, hc_in_d⟩ := hc_orig
      -- d cannot be horizontal_1_1 or horizontal_1_2 since (c.1+2, c.2) has column ≥ 3
      have hd_ne1 : d ≠ horizontal_1_1 := by
        intro heq
        subst heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton,
          horizontal_1_1_cell1, horizontal_1_1_cell2] at hc_in_d
        rcases hc_in_d with heq | heq
        · have := congrArg Prod.fst heq
          simp at this
        · have := congrArg Prod.fst heq
          simp at this
          omega
      have hd_ne2 : d ≠ horizontal_1_2 := by
        intro heq
        subst heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton,
          horizontal_1_2_cell1, horizontal_1_2_cell2] at hc_in_d
        rcases hc_in_d with heq | heq
        · have := congrArg Prod.fst heq
          simp at this
        · have := congrArg Prod.fst heq
          simp at this
          omega
      have hd_erase1 : d ∈ T.dominos.erase horizontal_1_1 := Finset.mem_erase.mpr ⟨hd_ne1, hd_mem⟩
      have hd_erase : d ∈ (T.dominos.erase horizontal_1_1).erase horizontal_1_2 :=
        Finset.mem_erase.mpr ⟨hd_ne2, hd_erase1⟩
      have hcols := other_dominos_col_ge_3 T hh1 hh2 d hd_mem hd_ne1 hd_ne2
      use d.shiftNeg 2 hcols.1 hcols.2
      constructor
      · use d, hd_erase
      · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d ⊢
        rcases hc_in_d with heq | heq
        · left
          simp only [Domino.shiftNeg_cell1]
          have hcol_eq := congrArg Prod.fst heq
          have hrow_eq := congrArg Prod.snd heq
          simp at hcol_eq hrow_eq
          ext <;> simp <;> omega
        · right
          simp only [Domino.shiftNeg_cell2]
          have hcol_eq := congrArg Prod.fst heq
          have hrow_eq := congrArg Prod.snd heq
          simp at hcol_eq hrow_eq
          ext <;> simp <;> omega
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hd1 hd2
    obtain ⟨d1', hd1'_erase, rfl⟩ := hd1
    obtain ⟨d2', hd2'_erase, rfl⟩ := hd2
    have hd1'_erase2 := Finset.mem_of_mem_erase hd1'_erase
    have hd2'_erase2 := Finset.mem_of_mem_erase hd2'_erase
    have hd1'_ne2 := (Finset.mem_erase.mp hd1'_erase).1
    have hd2'_ne2 := (Finset.mem_erase.mp hd2'_erase).1
    have hd1'_ne1 := (Finset.mem_erase.mp hd1'_erase2).1
    have hd2'_ne1 := (Finset.mem_erase.mp hd2'_erase2).1
    have hd1'_mem := Finset.mem_of_mem_erase hd1'_erase2
    have hd2'_mem := Finset.mem_of_mem_erase hd2'_erase2
    have hcols1 := other_dominos_col_ge_3 T hh1 hh2 d1' hd1'_mem hd1'_ne1 hd1'_ne2
    have hcols2 := other_dominos_col_ge_3 T hh1 hh2 d2' hd2'_mem hd2'_ne1 hd2'_ne2
    have hne' : d1' ≠ d2' := by
      intro heq
      apply hne
      subst heq
      rfl
    have hdisj := T.pairwise_disjoint d1' hd1'_mem d2' hd2'_mem hne'
    rw [Finset.disjoint_iff_ne] at hdisj ⊢
    intro c1 hc1 c2 hc2 heq
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
    rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
    · -- cell1 vs cell1
      simp only [Domino.shiftNeg_cell1, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell1 = d2'.cell1 := by ext <;> omega
      exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · -- cell1 vs cell2
      simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell1 = d2'.cell2 := by ext <;> omega
      exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig
    · -- cell2 vs cell1
      simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell2 = d2'.cell1 := by ext <;> omega
      exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · -- cell2 vs cell2
      simp only [Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell2 = d2'.cell2 := by ext <;> omega
      exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig


end DominoTiling
end DominoTilings
