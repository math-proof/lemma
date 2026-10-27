import Mathlib
import Theorem.Combinatorics.Tiling.DominoTilings.Part6
open Finset BigOperators


namespace DominoTilings

namespace DominoTiling

variable {n m : ℕ}


def restrictAfterVerticalGen (T : DominoTiling (n + 1) 2) (v : Domino)
    (hv : v ∈ T.dominos) (hv_cells : v.cells = vertical_1_1.cells) :
    DominoTiling n 2 where
  dominos := (T.dominos.erase v).attach.image fun ⟨d, hd⟩ =>
    let hd' := Finset.mem_erase.mp hd
    let hcols := domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d
                   (Finset.mem_of_mem_erase hd) hd'.1
    d.shiftNeg 1 hcols.1 hcols.2
  dominos_in_rect := by
    intro d' hd'
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hd'
    obtain ⟨d, hd_erase, rfl⟩ := hd'
    have hd_ne := (Finset.mem_erase.mp hd_erase).1
    have hd_mem := Finset.mem_of_mem_erase hd_erase
    have hcols := domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d hd_mem hd_ne
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
      have hcols := domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d hd_mem hd_ne
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
      have hc_orig : (c.1 + 1, c.2) ∈ Rectangle (n + 1) 2 := by
        rw [mem_Rectangle]
        omega
      rw [← T.covers_all] at hc_orig
      simp only [Finset.mem_biUnion] at hc_orig
      obtain ⟨d, hd_mem, hc_in_d⟩ := hc_orig
      have hd_ne : d ≠ v := by
        intro heq
        subst heq
        rw [hv_cells] at hc_in_d
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with heq | heq
        · have h1 := congrArg Prod.fst heq; simp at h1; omega
        · have h1 := congrArg Prod.fst heq; simp at h1; omega
      have hd_erase : d ∈ T.dominos.erase v := Finset.mem_erase.mpr ⟨hd_ne, hd_mem⟩
      have hcols := domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d hd_mem hd_ne
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
    have hcols1 := domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d1' hd1'_mem hd1'_ne
    have hcols2 := domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d2' hd2'_mem hd2'_ne
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
    · simp only [Domino.shiftNeg_cell1, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell1 = d2'.cell1 := by ext <;> omega
      exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell1 = d2'.cell2 := by ext <;> omega
      exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig
    · simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell2 = d2'.cell1 := by ext <;> omega
      exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · simp only [Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell2 = d2'.cell2 := by ext <;> omega
      exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig


end DominoTiling
end DominoTilings
