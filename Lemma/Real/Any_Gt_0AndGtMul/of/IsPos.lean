import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.le_mul](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {ε x : Chapter5.Real}
-- given
  (hε: ε.IsPos) :
-- imply
  ∃ M:ℕ, M > 0 ∧ M * ε > x :=
-- proof
  Chapter5.Real.le_mul hε x


-- created on 2026-10-22
