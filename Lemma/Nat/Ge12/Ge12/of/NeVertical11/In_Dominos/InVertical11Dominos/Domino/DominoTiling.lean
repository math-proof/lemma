import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
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
  (d : Domino)
  (hv : vertical_1_1 ∈ T.dominos)
  (hd : d ∈ T.dominos)
  (hne : d ≠ vertical_1_1) :
-- imply
  d.cell1.1 ≥ 2 ∧ d.cell2.1 ≥ 2 := by
-- proof
  have hdisj := T.pairwise_disjoint d hd vertical_1_1 hv hne
  rw [Finset.disjoint_iff_ne] at hdisj
  have hcols := Ge1.Ge1.of.InDominos.Domino.DominoTiling T d hd
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
      exact hdisj d.cell1 hc1_in_d vertical_1_1.cell1 (Finset.mem_insert_self _ _) (by simp [show d.cell1 = (1, 1) from Prod.ext h1 hr1])
    ·
      exact hdisj d.cell1 hc1_in_d vertical_1_1.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (by simp [show d.cell1 = (1, 2) from Prod.ext h1 hr2])
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
      exact hdisj d.cell2 hc2_in_d vertical_1_1.cell1 (Finset.mem_insert_self _ _) (by simp [show d.cell2 = (1, 1) from Prod.ext h2 hr1])
    ·
      exact hdisj d.cell2 hc2_in_d vertical_1_1.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (by simp [show d.cell2 = (1, 2) from Prod.ext h2 hr2])


-- created on 2026-10-20
