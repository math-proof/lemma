import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_1
open Section_4_1


/--
[mul_congr_right](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {a b c d c' d' : ℕ}
-- given
  (h: c —— d = c' —— d') :
-- imply
  (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') :=
-- proof
  Section_4_1.Int.mul_congr_right a b c d c' d' h


-- created on 2026-10-20
