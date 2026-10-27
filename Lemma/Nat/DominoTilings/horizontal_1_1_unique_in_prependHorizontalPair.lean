import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
import Lemma.Nat.Cell1Eq1Add.of.Domino
import Lemma.Nat.Cell2Eq1Add.of.Domino
import Lemma.Nat.Ge1.Ge1.of.InDominos.Domino.DominoTiling
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
  (T : DominoTiling n 2)
  (d : Domino)
  (hd : d ∈ (prependHorizontalPair T).dominos)
  (hd_cells : d.cells = ({(1, 1), (2, 1)} : Finset Cell)) :
-- imply
  d = horizontal_1_1 := by
-- proof
  simp only [prependHorizontalPair, Finset.mem_insert, Finset.mem_image] at hd
  obtain rfl | rfl | ⟨d', _, rfl⟩ := hd
  · rfl
  · -- d = horizontal_1_2, but horizontal_1_2.cells = {(1,2), (2,2)} ≠ {(1,1), (2,1)}
    simp only [Domino.cells, horizontal_1_2] at hd_cells
    have h : ((1, 2) : Cell) ∈ ({(1, 1), (2, 1)} : Finset Cell) := by
      rw [← hd_cells]; exact Finset.mem_insert_self _ _
    simp at h
  · -- d = d'.shiftNat 2, but shifted dominos have column ≥ 3
    have hcols := Ge1.Ge1.of.InDominos.Domino.DominoTiling T d' (by assumption)
    simp only [Domino.cells, Cell1Eq1Add.of.Domino, Cell2Eq1Add.of.Domino] at hd_cells
    have h : (d'.cell1.1 + 2, d'.cell1.2) ∈ ({(1, 1), (2, 1)} : Finset Cell) := by
      rw [← hd_cells]; exact Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨h, _⟩ | ⟨h, _⟩ := h <;> omega


-- created on 2026-10-20
