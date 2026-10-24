import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_epilogue
open Chapter5 hiding Real


/--
[isLowerSet_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_epilogue.lean)
-/
@[path]
private lemma main
  {E: Set ℚ} :
-- imply
  IsLowerSet E ↔ ∀ q r, r < q → q ∈ E → r ∈ E :=
-- proof
  Chapter5.isLowerSet_iff E


-- created on 2026-10-22
