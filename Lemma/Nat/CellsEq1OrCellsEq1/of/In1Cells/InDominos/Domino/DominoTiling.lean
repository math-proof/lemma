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
  (T : DominoTiling (n + 2) 2)
  (d : Domino)
  (hd : d ∈ T.dominos)
  (hcov : (1, 1) ∈ d.cells) :
-- imply
  d.cells = {(1, 1), (1, 2)} ∨ d.cells = {(1, 1), (2, 1)} := by
-- proof
  have hd_in := T.dominos_in_rect d hd
  have hc1_in := hd_in (Finset.mem_insert_self _ _)
  have hc2_in := hd_in (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at hc1_in hc2_in
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hcov
  obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
  ·
    left
    obtain heq | heq := hcov
    ·
      have hc1_1 : d.cell1.1 = 1 := congrArg Prod.fst heq.symm
      have hc1_2 : d.cell1.2 = 1 := congrArg Prod.snd heq.symm
      have hc2_1 : d.cell2.1 = 1 := by omega
      obtain h | h := hrow
      ·
        have hc2_2 : d.cell2.2 = 2 := by omega
        have hc2 : d.cell2 = (1, 2) := Prod.ext hc2_1 hc2_2
        simp only [Domino.cells, heq.symm, hc2]
      · omega
    ·
      have hc2_1 : d.cell2.1 = 1 := congrArg Prod.fst heq.symm
      have hc2_2 : d.cell2.2 = 1 := congrArg Prod.snd heq.symm
      have hc1_1 : d.cell1.1 = 1 := by omega
      obtain h | h := hrow
      · omega
      ·
        have hc1_2 : d.cell1.2 = 2 := by omega
        have hc1 : d.cell1 = (1, 2) := Prod.ext hc1_1 hc1_2
        simp only [Domino.cells, hc1, heq.symm, Finset.pair_comm]
  ·
    right
    obtain heq | heq := hcov
    ·
      have hc1_1 : d.cell1.1 = 1 := congrArg Prod.fst heq.symm
      have hc1_2 : d.cell1.2 = 1 := congrArg Prod.snd heq.symm
      have hc2_2 : d.cell2.2 = 1 := by omega
      obtain h | h := hcol
      ·
        have hc2_1 : d.cell2.1 = 2 := by omega
        have hc2 : d.cell2 = (2, 1) := Prod.ext hc2_1 hc2_2
        simp only [Domino.cells, heq.symm, hc2]
      · omega
    ·
      have hc2_1 : d.cell2.1 = 1 := congrArg Prod.fst heq.symm
      have hc2_2 : d.cell2.2 = 1 := congrArg Prod.snd heq.symm
      have hc1_2 : d.cell1.2 = 1 := by omega
      obtain h | h := hcol
      · omega
      ·
        have hc1_1 : d.cell1.1 = 2 := by omega
        have hc1 : d.cell1 = (2, 1) := Prod.ext hc1_1 hc1_2
        simp only [Domino.cells, hc1, heq.symm, Finset.pair_comm]


-- created on 2026-10-20
