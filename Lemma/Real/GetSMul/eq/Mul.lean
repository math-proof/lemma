import Mathlib
import sympy.Basic
import sympy.analysis.Section_9_2
open Chapter9


/--
[smul_func_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_2.lean)
-/
@[path]
private lemma main
  {c: ℝ}
  {f: ℝ → ℝ}
  {x: ℝ} :
-- imply
  (c • f) x = c * f x :=
-- proof
  Chapter9.smul_func_eval c f x


-- created on 2026-10-20
