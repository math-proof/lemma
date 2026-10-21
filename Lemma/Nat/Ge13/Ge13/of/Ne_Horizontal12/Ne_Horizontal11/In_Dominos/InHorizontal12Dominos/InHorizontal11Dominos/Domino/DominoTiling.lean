import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.Ge1.Ge1.of.InDominos.Domino.DominoTiling
import Lemma.Nat.IffIn_RectangleGe1AndGe_1AndGe21AndGe_2
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
  (T : DominoTiling (n + 2) 2)
  (d : Domino)
  (hh1 : horizontal_1_1 ∈ T.dominos)
  (hh2 : horizontal_1_2 ∈ T.dominos)
  (hd : d ∈ T.dominos)
  (hne1 : d ≠ horizontal_1_1)
  (hne2 : d ≠ horizontal_1_2) :
-- imply
  d.cell1.1 ≥ 3 ∧ d.cell2.1 ≥ 3 := by
-- proof
  have hdisj1 := T.pairwise_disjoint d hd horizontal_1_1 hh1 hne1
  have hdisj2 := T.pairwise_disjoint d hd horizontal_1_2 hh2 hne2
  have h := Ge1.Ge1.of.InDominos.Domino.DominoTiling T d hd
  constructor
  ·
    by_contra hlt
    push Not at hlt
    have hd_in_rect := T.dominos_in_rect d hd
    have hc1_in_rect := hd_in_rect (Finset.mem_insert_self _ _)
    rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at hc1_in_rect
    have hrow : d.cell1.2 = 1 ∨ d.cell1.2 = 2 := by omega
    obtain hr1 | hr2 := hrow
    ·
      have : d.cell1 ∈ horizontal_1_1.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        have hcol : d.cell1.1 = 1 ∨ d.cell1.1 = 2 := by omega
        obtain hc1 | hc2 := hcol
        ·
          left
          ext <;> simp [hc1, hr1]
        ·
          right
          ext <;> simp [hc2, hr1]
      exact Finset.disjoint_left.mp hdisj1 (Finset.mem_insert_self _ _) this
    ·
      have : d.cell1 ∈ horizontal_1_2.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        have hcol : d.cell1.1 = 1 ∨ d.cell1.1 = 2 := by omega
        obtain hc1 | hc2 := hcol
        ·
          left
          ext <;> simp [hc1, hr2]
        ·
          right
          ext <;> simp [hc2, hr2]
      exact Finset.disjoint_left.mp hdisj2 (Finset.mem_insert_self _ _) this
  ·
    by_contra hlt
    push Not at hlt
    have hd_in_rect := T.dominos_in_rect d hd
    have hc2_in_rect := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at hc2_in_rect
    have hrow : d.cell2.2 = 1 ∨ d.cell2.2 = 2 := by omega
    obtain hr1 | hr2 := hrow
    ·
      have : d.cell2 ∈ horizontal_1_1.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        have hcol : d.cell2.1 = 1 ∨ d.cell2.1 = 2 := by omega
        obtain hc1 | hc2 := hcol
        ·
          left
          ext <;> simp [hc1, hr1]
        ·
          right
          ext <;> simp [hc2, hr1]
      exact Finset.disjoint_left.mp hdisj1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) this
    ·
      have : d.cell2 ∈ horizontal_1_2.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        have hcol : d.cell2.1 = 1 ∨ d.cell2.1 = 2 := by omega
        obtain hc1 | hc2 := hcol
        ·
          left
          ext <;> simp [hc1, hr2]
        ·
          right
          ext <;> simp [hc2, hr2]
      exact Finset.disjoint_left.mp hdisj2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) this


-- created on 2026-10-20
