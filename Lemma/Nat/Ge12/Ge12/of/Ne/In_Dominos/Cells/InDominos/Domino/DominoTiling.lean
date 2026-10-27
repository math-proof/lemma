import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
import Lemma.Nat.DominoTilings.vertical_1_1_cells
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
  (T : DominoTiling (n + 1) 2)
  (v d : Domino)
  (hv : v ∈ T.dominos)
  (hv_cells : v.cells = vertical_1_1.cells)
  (hd : d ∈ T.dominos)
  (hne : d ≠ v) :
-- imply
  d.cell1.1 ≥ 2 ∧ d.cell2.1 ≥ 2 := by
-- proof
  have hdisj := T.pairwise_disjoint d hd v hv hne
  rw [Finset.disjoint_iff_ne] at hdisj
  have hcols := Ge1.Ge1.of.InDominos.Domino.DominoTiling T d hd
  -- v covers (1,1) and (1,2)
  have hv_11 : (1, 1) ∈ v.cells := by rw [hv_cells]; simp [DominoTilings.vertical_1_1_cells]
  have hv_12 : (1, 2) ∈ v.cells := by rw [hv_cells]; simp [DominoTilings.vertical_1_1_cells]
  constructor
  ·
    by_contra h
    push Not at h
    have h1 : d.cell1.1 = 1 := by omega
    have hd_in := T.dominos_in_rect d hd
    have hc1_in_d : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
    have hc1_in_rect := hd_in hc1_in_d
    rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at hc1_in_rect
    have hrow_bound : d.cell1.2 = 1 ∨ d.cell1.2 = 2 := by omega
    obtain hr1 | hr2 := hrow_bound
    ·
      exact hdisj d.cell1 hc1_in_d (1, 1) hv_11 (Prod.ext h1 hr1)
    ·
      exact hdisj d.cell1 hc1_in_d (1, 2) hv_12 (Prod.ext h1 hr2)
  ·
    by_contra h
    push Not at h
    have h2 : d.cell2.1 = 1 := by omega
    have hd_in := T.dominos_in_rect d hd
    have hc2_in_d : d.cell2 ∈ d.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hc2_in_rect := hd_in hc2_in_d
    rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at hc2_in_rect
    have hrow_bound : d.cell2.2 = 1 ∨ d.cell2.2 = 2 := by omega
    obtain hr1 | hr2 := hrow_bound
    ·
      exact hdisj d.cell2 hc2_in_d (1, 1) hv_11 (Prod.ext h2 hr1)
    ·
      exact hdisj d.cell2 hc2_in_d (1, 2) hv_12 (Prod.ext h2 hr2)


-- created on 2026-10-20
