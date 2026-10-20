import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_1
open Chapter5


/--
[n0_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {a: ℕ → ℚ} :
-- imply
  (a:Sequence).n₀ = 0 :=
-- proof
  Chapter5.Sequence.n0_coe a


-- created on 2026-10-20
