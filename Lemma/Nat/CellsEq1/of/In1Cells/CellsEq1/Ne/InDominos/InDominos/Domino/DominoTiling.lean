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
  (T : DominoTiling (n + 2) 2)
  (d d' : Domino)
  (hd : d ∈ T.dominos)
  (hd' : d' ∈ T.dominos)
  (hne : d' ≠ d)
  (hd_cells : d.cells = {(1, 1), (2, 1)})
  (hd'_cov : (1, 2) ∈ d'.cells) :
-- imply
  d'.cells = {(1, 2), (2, 2)} := by
-- proof
  have hdisj := T.pairwise_disjoint d' hd' d hd hne
  have hd'_not_11 : (1, 1) ∉ d'.cells := by
    intro h
    rw [Finset.disjoint_iff_ne] at hdisj
    have h11_in_d : (1, 1) ∈ d.cells := by rw [hd_cells]; simp
    exact hdisj (1, 1) h (1, 1) h11_in_d rfl
  have hd'_not_21 : (2, 1) ∉ d'.cells := by
    intro h
    rw [Finset.disjoint_iff_ne] at hdisj
    have h21_in_d : (2, 1) ∈ d.cells := by rw [hd_cells]; simp
    exact hdisj (2, 1) h (2, 1) h21_in_d rfl
  have hd'_in := T.dominos_in_rect d' hd'
  have hc1_in := hd'_in (Finset.mem_insert_self _ _)
  have hc2_in := hd'_in (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [mem_Rectangle] at hc1_in hc2_in
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd'_cov
  obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d'.adjacent
  ·
    -- d' is vertical
    obtain heq | heq := hd'_cov
    ·
      have hc1_1 : d'.cell1.1 = 1 := congrArg Prod.fst heq.symm
      have hc1_2 : d'.cell1.2 = 2 := congrArg Prod.snd heq.symm
      have hc2_1 : d'.cell2.1 = 1 := by omega
      obtain h | h := hrow
      · omega
      ·
        have hc2_2 : d'.cell2.2 = 1 := by omega
        have hc2 : d'.cell2 = (1, 1) := Prod.ext hc2_1 hc2_2
        have h11_in_d' : (1, 1) ∈ d'.cells := by
          simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
          right; exact hc2.symm
        exact absurd h11_in_d' hd'_not_11
    ·
      have hc2_1 : d'.cell2.1 = 1 := congrArg Prod.fst heq.symm
      have hc2_2 : d'.cell2.2 = 2 := congrArg Prod.snd heq.symm
      have hc1_1 : d'.cell1.1 = 1 := by omega
      obtain h | h := hrow
      ·
        have hc1_2' : d'.cell1.2 = 1 := by omega
        have hc1 : d'.cell1 = (1, 1) := Prod.ext hc1_1 hc1_2'
        have h11_in_d' : (1, 1) ∈ d'.cells := by
          simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
          left; exact hc1.symm
        exact absurd h11_in_d' hd'_not_11
      · omega
  ·
    -- d' is horizontal
    obtain heq | heq := hd'_cov
    ·
      have hc1_1 : d'.cell1.1 = 1 := congrArg Prod.fst heq.symm
      have hc1_2 : d'.cell1.2 = 2 := congrArg Prod.snd heq.symm
      have hc2_2 : d'.cell2.2 = 2 := by omega
      obtain h | h := hcol
      ·
        have hc2_1 : d'.cell2.1 = 2 := by omega
        have hc2 : d'.cell2 = (2, 2) := Prod.ext hc2_1 hc2_2
        simp only [Domino.cells, heq.symm, hc2]
      · omega
    ·
      have hc2_1 : d'.cell2.1 = 1 := congrArg Prod.fst heq.symm
      have hc2_2 : d'.cell2.2 = 2 := congrArg Prod.snd heq.symm
      have hc1_2 : d'.cell1.2 = 2 := by omega
      obtain h | h := hcol
      · omega
      ·
        have hc1_1 : d'.cell1.1 = 2 := by omega
        have hc1 : d'.cell1 = (2, 2) := Prod.ext hc1_1 hc1_2
        simp only [Domino.cells, hc1, heq.symm, Finset.pair_comm]


-- created on 2026-10-20
