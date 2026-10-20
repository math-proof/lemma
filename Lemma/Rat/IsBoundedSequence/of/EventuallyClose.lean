import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_2
open Chapter5


/--
[isBounded_of_eventuallyClose](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_2.lean)
-/
@[path]
private lemma main
  {ε:ℚ}
  {a b: ℕ → ℚ}
-- given
  (hab: ε.EventuallyClose a b) :
-- imply
  (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded :=
-- proof
  Chapter5.Sequence.isBounded_of_eventuallyClose hab


-- created on 2026-10-20
