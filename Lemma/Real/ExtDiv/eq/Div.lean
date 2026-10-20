import Mathlib
import sympy.Basic
import sympy.analysis.Section_9_2
open Chapter9


/--
[div_func_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_2.lean)
-/
@[path]
private lemma main
  {f g: ℝ → ℝ}
  {x: ℝ} :
-- imply
  (f / g) x = f x / g x :=
-- proof
  Chapter9.div_func_eval f g x


-- created on 2026-10-20
