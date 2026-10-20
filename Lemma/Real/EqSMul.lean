import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_2
open Chapter7


/--
[smul_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_2.lean)
-/
@[path]
private lemma main
  {a: ℕ → ℝ}
  {c: ℝ} :
-- imply
  (c • a:Series) = (fun n ↦ c * a n) :=
-- proof
  Chapter7.Series.smul_coe a c


-- created on 2026-10-20
