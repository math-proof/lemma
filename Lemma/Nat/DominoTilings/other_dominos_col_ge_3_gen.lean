import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
import Lemma.Nat.Ge1.Ge1.of.InDominos.Domino.DominoTiling
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
  (d1 d2 d : Domino)
  (hd1 : d1 ∈ T.dominos)
  (hd2 : d2 ∈ T.dominos)
  (hd1_cells : d1.cells = ({(1, 1), (2, 1)} : Finset Cell))
  (hd2_cells : d2.cells = ({(1, 2), (2, 2)} : Finset Cell))
  (hd : d ∈ T.dominos)
  (hne1 : d ≠ d1)
  (hne2 : d ≠ d2) :
-- imply
  d.cell1.1 ≥ 3 ∧ d.cell2.1 ≥ 3 := by
-- proof
  have hdisj1 := T.pairwise_disjoint d hd d1 hd1 hne1
  have hdisj2 := T.pairwise_disjoint d hd d2 hd2 hne2
  rw [Finset.disjoint_iff_ne] at hdisj1 hdisj2
  have hcols := Ge1.Ge1.of.InDominos.Domino.DominoTiling T d hd
  -- d1 covers (1,1) and (2,1), d2 covers (1,2) and (2,2)
  have h11 : (1, 1) ∈ d1.cells := by rw [hd1_cells]; simp
  have h21 : (2, 1) ∈ d1.cells := by rw [hd1_cells]; simp
  have h12 : (1, 2) ∈ d2.cells := by rw [hd2_cells]; simp
  have h22 : (2, 2) ∈ d2.cells := by rw [hd2_cells]; simp
  have hd_in := T.dominos_in_rect d hd
  constructor
  ·
    by_contra h
    push Not at h
    have hc1_col : d.cell1.1 = 1 ∨ d.cell1.1 = 2 := by omega
    have hc1_in_d : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
    have hc1_in_rect := hd_in hc1_in_d
    rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at hc1_in_rect
    have hrow_bound : d.cell1.2 = 1 ∨ d.cell1.2 = 2 := by omega
    obtain hcol1 | hcol2 := hc1_col <;> obtain hr1 | hr2 := hrow_bound
    ·
      exact hdisj1 d.cell1 hc1_in_d (1, 1) h11 (Prod.ext hcol1 hr1)
    ·
      exact hdisj2 d.cell1 hc1_in_d (1, 2) h12 (Prod.ext hcol1 hr2)
    ·
      exact hdisj1 d.cell1 hc1_in_d (2, 1) h21 (Prod.ext hcol2 hr1)
    ·
      exact hdisj2 d.cell1 hc1_in_d (2, 2) h22 (Prod.ext hcol2 hr2)
  ·
    by_contra h
    push Not at h
    have hc2_col : d.cell2.1 = 1 ∨ d.cell2.1 = 2 := by omega
    have hc2_in_d : d.cell2 ∈ d.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hc2_in_rect := hd_in hc2_in_d
    rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at hc2_in_rect
    have hrow_bound : d.cell2.2 = 1 ∨ d.cell2.2 = 2 := by omega
    obtain hcol1 | hcol2 := hc2_col <;> obtain hr1 | hr2 := hrow_bound
    ·
      exact hdisj1 d.cell2 hc2_in_d (1, 1) h11 (Prod.ext hcol1 hr1)
    ·
      exact hdisj2 d.cell2 hc2_in_d (1, 2) h12 (Prod.ext hcol1 hr2)
    ·
      exact hdisj1 d.cell2 hc2_in_d (2, 1) h21 (Prod.ext hcol2 hr1)
    ·
      exact hdisj2 d.cell2 hc2_in_d (2, 2) h22 (Prod.ext hcol2 hr2)


-- created on 2026-10-20
