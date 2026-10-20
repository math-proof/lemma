import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[mul_pow](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x y:ℚ}
  {n:ℕ} :
-- imply
  (x*y)^n = x^n * y^n :=
-- proof
  Section_4_3.mul_pow x y n


-- created on 2026-10-20
