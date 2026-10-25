import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Sequence


/--
[Sequence.convergent_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a:Sequence} :
-- imply
  a.Convergent ↔ ∃ L, a.TendsTo L :=
-- proof
  Chapter6.Sequence.convergent_def a


-- created on 2026-10-22
