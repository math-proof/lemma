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
  (k : ℕ) :
-- imply
  Function.Injective (fun d : Domino => d.shiftNat k) := by
-- proof
  intro d1 d2 h
  simp only [Domino.ext_iff, shiftNat_cell1, shiftNat_cell2, Prod.mk.injEq] at h
  ext <;> omega


-- created on 2026-10-20
