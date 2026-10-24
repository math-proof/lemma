import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_1
open Chapter6
open Chapter6.Sequence


/--
[Sequence.divergent_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a:Sequence} :
-- imply
  a.Divergent ↔ ¬ a.Convergent :=
-- proof
  Chapter6.Sequence.divergent_def a


-- created on 2026-10-22
