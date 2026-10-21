import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.Cell1Eq1Add.of.Domino
import Lemma.Nat.Cell2Eq1Add.of.Domino
import Lemma.Nat.DominoTilings.horizontalPair_of_not_hasVerticalFirstColumn
import Lemma.Nat.DominoTilings.horizontal_1_1_unique_in_prependHorizontalPair
import Lemma.Nat.DominoTilings.horizontal_1_2_unique_in_prependHorizontalPair
import Lemma.Nat.DominoTilings.vertical_1_1_unique_in_prependVertical
import Lemma.Nat.Ge1.Ge1.of.InDominos.Domino.DominoTiling
import Lemma.Nat.DominoTilings.restrictAfterVerticalGen_eq_restrictAfterVertical
import Lemma.Nat.DominoTilings.restrictAfterHorizontalPair_prependHorizontalPair
import Lemma.Nat.DominoTilings.restrictAfterVertical_prependVertical
open DominoTilings
open Domino DominoTiling
open Finset
open Nat
set_option linter.unusedSimpArgs false


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (x : (DominoTiling n 2) ⊕ (DominoTiling (n + 1) 2)) :
-- imply
  tiling_2_to_sum (tiling_2_from_sum x) = x := by
-- proof
  unfold tiling_2_to_sum tiling_2_from_sum
  obtain T | T := x
  · -- Horizontal case: x = inl T
    rw [Sum.elim_inl]
    -- prependHorizontalPair produces a tiling without vertical first column
    have hv : ¬hasVerticalFirstColumn (prependHorizontalPair T) := by
      intro ⟨d, hd_mem, hd_cells⟩
      simp only [prependHorizontalPair, Finset.mem_insert, Finset.mem_image] at hd_mem
      obtain rfl | rfl | ⟨d', _, rfl⟩ := hd_mem
      · -- d = horizontal_1_1: cells = {(1,1), (2,1)} ≠ {(1,1), (1,2)}
        simp only [Domino.cells, horizontal_1_1] at hd_cells
        have h1 : ((1, 1) : Cell) ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
          rw [← hd_cells]; exact Finset.mem_insert_self _ _
        have h2 : ((2, 1) : Cell) ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
          rw [← hd_cells]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h2
        obtain ⟨h, _⟩ | ⟨h, _⟩ := h2 <;> omega
      · -- d = horizontal_1_2: cells = {(1,2), (2,2)} ≠ {(1,1), (1,2)}
        simp only [Domino.cells, horizontal_1_2] at hd_cells
        have h2 : ((2, 2) : Cell) ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
          rw [← hd_cells]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h2
        obtain ⟨h, _⟩ | ⟨h, _⟩ := h2 <;> omega
      · -- d = d'.shiftNat 2: cells have column ≥ 3
        have hcols := Ge1.Ge1.of.InDominos.Domino.DominoTiling T d' (by assumption)
        simp only [Domino.cells, Cell1Eq1Add.of.Domino, Cell2Eq1Add.of.Domino] at hd_cells
        have h1 : (d'.cell1.1 + 2, d'.cell1.2) ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
          rw [← hd_cells]; exact Finset.mem_insert_self _ _
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1
        obtain ⟨h, _⟩ | ⟨h, _⟩ := h1 <;> omega
    simp only [dite_eq_right hv]
    -- The chosen dominos must be horizontal_1_1 and horizontal_1_2 by uniqueness
    have hpair := DominoTilings.horizontalPair_of_not_hasVerticalFirstColumn (prependHorizontalPair T) hv
    have hd1_spec := Classical.choose_spec hpair.1
    have hd2_spec := Classical.choose_spec hpair.2
    have hd1_eq : Classical.choose hpair.1 = horizontal_1_1 :=
      _root_.Nat.DominoTilings.horizontal_1_1_unique_in_prependHorizontalPair T _ hd1_spec.1 hd1_spec.2
    have hd2_eq : Classical.choose hpair.2 = horizontal_1_2 :=
      _root_.Nat.DominoTilings.horizontal_1_2_unique_in_prependHorizontalPair T _ hd2_spec.1 hd2_spec.2
    -- Now use the existing roundtrip lemma
    simp only [hd1_eq, hd2_eq]
    have hmem1 : horizontal_1_1 ∈ (prependHorizontalPair T).dominos := by
      simp [prependHorizontalPair]
    have hmem2 : horizontal_1_2 ∈ (prependHorizontalPair T).dominos := by
      simp [prependHorizontalPair]
    -- The Gen version with canonical dominos equals the non-Gen version
    congr 1
    conv_lhs => rw [show restrictAfterHorizontalPairGen (prependHorizontalPair T) horizontal_1_1
      horizontal_1_2 hmem1 hmem2 rfl rfl = restrictAfterHorizontalPair (prependHorizontalPair T)
      hmem1 hmem2 from rfl]
    exact _root_.Nat.DominoTilings.restrictAfterHorizontalPair_prependHorizontalPair T
  · -- Vertical case: x = inr T
    rw [Sum.elim_inr]
    -- prependVertical produces a tiling with vertical first column
    have hv : hasVerticalFirstColumn (prependVertical T) := by
      use vertical_1_1
      constructor
      · simp [prependVertical, vertical_1_1]
      · rfl
    simp only [dite_eq_left hv]
    -- The chosen domino must be vertical_1_1 by uniqueness
    have hv_spec := Classical.choose_spec hv
    have hv_eq : Classical.choose hv = vertical_1_1 :=
      _root_.Nat.DominoTilings.vertical_1_1_unique_in_prependVertical T _ hv_spec.1 hv_spec.2
    simp only [hv_eq]
    have hmem : vertical_1_1 ∈ (prependVertical T).dominos := by
      simp [prependVertical]
    -- The Gen version with canonical domino equals the non-Gen version
    congr 1
    conv_lhs => rw [show restrictAfterVerticalGen (prependVertical T) vertical_1_1
      hmem rfl = restrictAfterVertical (prependVertical T) hmem from
      _root_.Nat.DominoTilings.restrictAfterVerticalGen_eq_restrictAfterVertical (prependVertical T) hmem]
    exact _root_.Nat.DominoTilings.restrictAfterVertical_prependVertical T


-- created on 2026-10-20
