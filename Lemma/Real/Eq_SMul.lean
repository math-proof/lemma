import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_1
open Chapter6
open Chapter6.Sequence


/--
[Sequence.smul_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {c:ℝ}
  {a:ℕ → ℝ} :
-- imply
  (c • (a:Sequence)) = (fun n ↦ c * a n) :=
-- proof
  Chapter6.Sequence.smul_coe c a


-- created on 2026-10-22
