import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_4_1.Part8
open Section_4_1


/--
[mul_congr](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {a b c d a' b' c' d' : ℕ}
-- given
  (h0: a —— b = a' —— b')
  (h1: c —— d = c' —— d') :
-- imply
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') :=
-- proof
  Section_4_1.Int.mul_congr h0 h1


-- created on 2026-10-20
