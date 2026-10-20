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
  (S : Finset Domino)
  (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
-- imply
  vertical_1_1 ∉ S.image (fun d => d.shiftNat 2) := by
-- proof
  simp only [Finset.mem_image, not_exists, not_and]
  intro d hd h
  have h1 := congrArg Domino.cell1 h
  simp only [Domino.shiftNat_cell1, vertical_1_1_cell1, Prod.mk.injEq] at h1
  have hd_pos := (hS d hd).1
  omega


-- created on 2026-10-20
