import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_1
open Chapter5


/--
[isBounded_sub](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {a b:ℕ → ℚ}
-- given
  (ha: (a:Sequence).IsBounded)
  (hb: (b:Sequence).IsBounded) :
-- imply
  (a - b:Sequence).IsBounded :=
-- proof
  Chapter5.Sequence.isBounded_sub ha hb


-- created on 2026-10-20
