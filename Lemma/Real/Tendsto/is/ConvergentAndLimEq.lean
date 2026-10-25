import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Sequence

/--
[Sequence.lim_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a:Sequence}
  {L:ℝ} :
-- imply
  a.TendsTo L ↔ a.Convergent ∧ lim a = L :=
-- proof
  Chapter6.Sequence.lim_eq

-- created on 2026-10-22
