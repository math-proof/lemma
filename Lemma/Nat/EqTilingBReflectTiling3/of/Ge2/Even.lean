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
  (n : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2) :
-- imply
  TilingB n hn hn_ge = reflectTiling3 (TilingA n hn hn_ge) := by
-- proof
  exact DominoTilings.TilingB_eq_reflectTiling3_TilingA n hn hn_ge


-- created on 2026-10-20
