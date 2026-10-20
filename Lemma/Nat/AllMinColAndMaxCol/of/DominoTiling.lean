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
  {n : ℕ}
-- given
  (T : DominoTiling n 3) :
-- imply
  ∀ d ∈ T.dominos, ∃ d' ∈ (reflectTiling3 T).dominos, d'.minCol = d.minCol ∧ d'.maxCol = d.maxCol := by
-- proof
  intro d hd
  -- The reflected domino d' is reflectDomino3 d
  let h1 := domino_cell1_row_le' (T.dominos_in_rect d hd)
  let h2 := domino_cell2_row_le' (T.dominos_in_rect d hd)
  use reflectDomino3 d h1 h2
  constructor
  ·
    -- Show d' is in (reflectTiling3 T).dominos
    simp only [reflectTiling3, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
      ← Function.Embedding.toFun_eq_coe]
    exact ⟨d, hd, rfl⟩
  ·
    -- Show minCol and maxCol are preserved
    exact ⟨reflectDomino3_minCol h1 h2, reflectDomino3_maxCol h1 h2⟩


-- created on 2026-10-20
