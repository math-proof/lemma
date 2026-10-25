import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_9_2.Part2
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
