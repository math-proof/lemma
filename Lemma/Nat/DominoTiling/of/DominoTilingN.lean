import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings
import Lemma.Nat.EqDomino.of.Ge1.Ge1.Domino
import Lemma.Nat.Ge1.Ge1.of.InDominos.Domino.DominoTiling
import Lemma.Nat.Ge13.Ge13.of.Ne_Horizontal12.Ne_Horizontal11.In_Dominos.InHorizontal12Dominos.InHorizontal11Dominos.Domino.DominoTiling
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
  (T : DominoTiling n 2) :
-- imply
  restrictAfterHorizontalPair (prependHorizontalPair T)
    (by simp [prependHorizontalPair, horizontal_1_1])
      (by simp [prependHorizontalPair, horizontal_1_2]) = T := by
-- proof
  cases T with | mk dominos dominos_in_rect covers_all pairwise_disjoint =>
    unfold prependHorizontalPair restrictAfterHorizontalPair
    congr 1
    ext d
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    constructor
    ·
      -- Forward: d is in the result of restrictAfterHorizontalPair (prependHorizontalPair T)
      intro hd
      obtain ⟨d', hd'_erase, hd'_eq⟩ := hd -- d' is in ((insert horizontal_1_1 (insert horizontal_1_2 (dominos.image (fun d => d.shiftNat 2)))).erase horizontal_1_1).erase horizontal_1_2
      have hd'_ne1 : d' ≠ horizontal_1_1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hd'_erase)).1
      have hd'_ne2 : d' ≠ horizontal_1_2 := (Finset.mem_erase.mp hd'_erase).1
      have hd'_mem : d' ∈ insert horizontal_1_1 (insert horizontal_1_2 (dominos.image (fun d => d.shiftNat 2))) :=
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd'_erase)
      rw [Finset.mem_insert] at hd'_mem
      obtain rfl | hd'_mem' := hd'_mem
      · exact absurd rfl hd'_ne1
      ·
        rw [Finset.mem_insert] at hd'_mem'
        obtain rfl | hd'_in_image := hd'_mem'
        · exact absurd rfl hd'_ne2
        ·
          simp only [Finset.mem_image] at hd'_in_image
          obtain ⟨d'', hd''_mem, hd''_eq⟩ := hd'_in_image
          have hcols := Ge1.Ge1.of.InDominos.Domino.DominoTiling
            ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ d'' hd''_mem
          subst hd''_eq
          rw [← hd'_eq] -- Show (d''.shiftNat 2).shiftNeg 2 ... = d''
          have h_eq : (d''.shiftNat 2).shiftNeg 2
            (Ge13.Ge13.of.Ne_Horizontal12.Ne_Horizontal11.In_Dominos.InHorizontal12Dominos.InHorizontal11Dominos.Domino.DominoTiling (prependHorizontalPair ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩)
                (d''.shiftNat 2)
                (by simp [prependHorizontalPair, horizontal_1_1])
                (by simp [prependHorizontalPair, horizontal_1_2])
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd'_erase))
                hd'_ne1 hd'_ne2).1
              (Ge13.Ge13.of.Ne_Horizontal12.Ne_Horizontal11.In_Dominos.InHorizontal12Dominos.InHorizontal11Dominos.Domino.DominoTiling (prependHorizontalPair ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩)
                (d''.shiftNat 2)
                (by simp [prependHorizontalPair, horizontal_1_1])
                (by simp [prependHorizontalPair, horizontal_1_2])
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd'_erase))
                hd'_ne1 hd'_ne2).2 = d'' := by
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
      have hcols := Ge1.Ge1.of.InDominos.Domino.DominoTiling
        ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ d hd
      have hne1 : d.shiftNat 2 ≠ horizontal_1_1 := by
        intro h
        have h1 := congrArg (·.cell1.1) h
        simp [Domino.shiftNat, horizontal_1_1] at h1
      have hne2 : d.shiftNat 2 ≠ horizontal_1_2 := by
        intro h
        have h1 := congrArg (·.cell1.1) h
        simp [Domino.shiftNat, horizontal_1_2] at h1
      have hmem : d.shiftNat 2 ∈ dominos.image (fun d => d.shiftNat 2) :=
        Finset.mem_image_of_mem _ hd
      have hmem' : d.shiftNat 2 ∈ insert horizontal_1_2 (dominos.image (fun d => d.shiftNat 2)) :=
        Finset.mem_insert_of_mem hmem
      have hmem'' : d.shiftNat 2 ∈ insert horizontal_1_1 (insert horizontal_1_2 (dominos.image (fun d => d.shiftNat 2))) :=
        Finset.mem_insert_of_mem hmem'
      have hmem1 : d.shiftNat 2 ∈ (insert horizontal_1_1 (insert horizontal_1_2 (dominos.image (fun d => d.shiftNat 2)))).erase horizontal_1_1 :=
        Finset.mem_erase.mpr ⟨hne1, hmem''⟩
      have hmem2 : d.shiftNat 2 ∈ ((insert horizontal_1_1 (insert horizontal_1_2 (dominos.image (fun d => d.shiftNat 2)))).erase horizontal_1_1).erase horizontal_1_2 :=
        Finset.mem_erase.mpr ⟨hne2, hmem1⟩
      use d.shiftNat 2, hmem2
      exact EqDomino.of.Ge1.Ge1.Domino d hcols.1 hcols.2 2


-- created on 2026-10-20
