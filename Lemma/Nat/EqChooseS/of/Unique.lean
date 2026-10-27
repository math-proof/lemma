import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Tools.ExistsUnique.Part2


/--
[choose_eq_choose](https://github.com/teorth/analysis/blob/main/Analysis/Tools/ExistsUnique.lean)
-/
@[path]
private lemma main
  {p: α → Prop}
-- given
  (h : ∃! x, p x) :
-- imply
  Exists.choose h = h.choose :=
-- proof
  ExistsUnique.choose_eq_choose h


-- created on 2026-10-20
