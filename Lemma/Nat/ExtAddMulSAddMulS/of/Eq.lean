import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_4_1.Part8
open Section_4_1


/--
[mul_congr_left](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {a b a' b' c d : ℕ}
-- given
  (h: a —— b = a' —— b') :
-- imply
  (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) :=
-- proof
  Section_4_1.Int.mul_congr_left a b a' b' c d h


-- created on 2026-10-20
