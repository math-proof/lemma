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
  {T₁ T₂ T₃ : DominoTiling n m}
-- given
  (h₁ : TilingEquiv T₁ T₂)
  (h₂ : TilingEquiv T₂ T₃) :
-- imply
  TilingEquiv T₁ T₃ :=
-- proof
  h₁.trans h₂


-- created on 2026-10-20
