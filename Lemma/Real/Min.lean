import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_9_2.Part2
open Chapter9


/--
[min_func_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_2.lean)
-/
@[path]
private lemma main
  {f g: ℝ → ℝ}
  {x: ℝ} :
-- imply
  min f g x = min (f x) (g x) :=
-- proof
  Chapter9.min_func_eval f g x


-- created on 2026-10-20
