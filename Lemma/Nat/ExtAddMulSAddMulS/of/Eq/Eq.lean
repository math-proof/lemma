import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_1
open Section_4_1


/--
[mul_congr](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {a b c d a' b' c' d' : ℕ}
-- given
  (h1: a —— b = a' —— b')
  (h2: c —— d = c' —— d') :
-- imply
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') :=
-- proof
  Section_4_1.Int.mul_congr h1 h2


-- created on 2026-10-20
