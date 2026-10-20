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
  (T : DominoTiling n m)
  (c : Cell)
  (hc : c ∈ Rectangle n m) :
-- imply
  ∃ d ∈ T.dominos, c ∈ d.cells := by
-- proof
  rw [← T.covers_all] at hc
  simp only [Finset.mem_biUnion] at hc
  exact hc


-- created on 2026-10-20
