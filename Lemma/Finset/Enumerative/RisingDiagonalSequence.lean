import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.RisingDiagonalSequence
open MetaMathlibExt


/--
[risingDiagonal_const](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RisingDiagonalSequence.lean)
-/
@[path]
private lemma risingDiagonal_const_eq
  {a : ℕ → ℕ → ℝ}
  {a₀ a₁ α β : ℝ}
  {n : ℕ}
  {i j : Fin (n / 2 + 1)}
-- given
  (h : IsBinaryBinomialInterpolatedTriangle a a₀ a₁ α β) :
-- imply
  risingDiagonal a n i = risingDiagonal a n j := by
-- proof
  apply MetaMathlibExt.risingDiagonal_const h n i j


-- created on 2026-10-20
