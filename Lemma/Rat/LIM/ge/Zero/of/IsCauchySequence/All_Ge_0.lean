import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.LIM_of_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {a: ℕ → ℚ}
-- given
  (ha: ∀ n, a n ≥ 0)
  (hcauchy: (a:Sequence).IsCauchy) :
-- imply
  LIM a ≥ 0 :=
-- proof
  Chapter5.Real.LIM_of_nonneg ha hcauchy


-- created on 2026-10-22
