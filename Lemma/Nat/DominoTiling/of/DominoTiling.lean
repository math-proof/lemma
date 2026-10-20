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
  (T : DominoTiling n 2) :
-- imply
  restrictAfterVertical (prependVertical T) (by simp [prependVertical, vertical_1_1]) = T := by
-- proof
  cases T with | mk dominos dominos_in_rect covers_all pairwise_disjoint =>
    unfold prependVertical restrictAfterVertical
    congr 1
    ext d
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    constructor
    ·
      -- Forward: d is in the result of restrictAfterVertical (prependVertical T)
      intro hd
      obtain ⟨d', hd'_erase, hd'_eq⟩ := hd
      have hd'_ne : d' ≠ vertical_1_1 := (Finset.mem_erase.mp hd'_erase).1
      have hd'_mem : d' ∈ insert vertical_1_1 (dominos.image (fun d => d.shiftNat 1)) :=
        Finset.mem_of_mem_erase hd'_erase
      rw [Finset.mem_insert] at hd'_mem
      obtain rfl | hd'_in_image := hd'_mem
      · exact absurd rfl hd'_ne
      ·
        simp only [Finset.mem_image] at hd'_in_image
        obtain ⟨d'', hd''_mem, hd''_eq⟩ := hd'_in_image
        have hcols := domino_cells_col_ge_one
          ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ d'' hd''_mem
        subst hd''_eq
        rw [← hd'_eq] -- Show (d''.shiftNat 1).shiftNeg 1 ... = d'' by extensionality
        have h_eq : (d''.shiftNat 1).shiftNeg 1
          (domino_col_ge_two_of_ne_vertical (prependVertical ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩)
              (by simp [prependVertical, vertical_1_1])
              (d''.shiftNat 1)
              (Finset.mem_of_mem_erase hd'_erase)
              hd'_ne).1
            (domino_col_ge_two_of_ne_vertical (prependVertical ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩)
              (by simp [prependVertical, vertical_1_1])
              (d''.shiftNat 1)
              (Finset.mem_of_mem_erase hd'_erase)
              hd'_ne).2 = d'' := by
          apply Domino.ext
          ·
            simp only [Domino.shiftNeg, Domino.shiftNat]
            simp only [Nat.add_sub_cancel]
          ·
            simp only [Domino.shiftNeg, Domino.shiftNat]
            simp only [Nat.add_sub_cancel]
        rwa [h_eq]
    ·
      -- Backward: d ∈ dominos → d is in the result
      intro hd
      have hcols := domino_cells_col_ge_one
        ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ d hd
      have hne : d.shiftNat 1 ≠ vertical_1_1 := by
        intro h
        have h1 := congrArg (·.cell1.1) h
        simp [Domino.shiftNat, vertical_1_1] at h1
        omega
      have hmem : d.shiftNat 1 ∈ dominos.image (fun d => d.shiftNat 1) :=
        Finset.mem_image_of_mem _ hd
      have hmem' : d.shiftNat 1 ∈ insert vertical_1_1 (dominos.image (fun d => d.shiftNat 1)) :=
        Finset.mem_insert_of_mem hmem
      have hmem'' : d.shiftNat 1 ∈ (insert vertical_1_1 (dominos.image (fun d => d.shiftNat 1))).erase vertical_1_1 :=
        Finset.mem_erase.mpr ⟨hne, hmem'⟩
      use d.shiftNat 1, hmem''
      exact Domino.shiftNeg_shiftNat d 1 hcols.1 hcols.2


-- created on 2026-10-20
