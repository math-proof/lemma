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
  (T₁ T₂ : DominoTiling n 3)
  (h : DominoTiling.TilingEquiv T₁ T₂) :
-- imply
  DominoTiling.TilingEquiv (reflectTiling3 T₁) (reflectTiling3 T₂) := by
-- proof
  exact DominoTilings.reflectTiling3_preserves_TilingEquiv T₁ T₂ h


-- created on 2026-10-20
