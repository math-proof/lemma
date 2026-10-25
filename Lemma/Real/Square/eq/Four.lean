import Mathlib
import sympy.Basic
import Theorem.Analysis.Appendix_A_2


/--
[imp_example](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_A_2.lean)
-/
@[path]
private lemma main
  {x:ℝ} :
-- imply
  (x = 2) → (x^2 = 4) :=
-- proof
  imp_example x


-- created on 2026-10-20
