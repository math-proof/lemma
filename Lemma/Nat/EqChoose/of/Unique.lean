import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Tools.ExistsUnique.Part2


/--
[choose_eq](https://github.com/teorth/analysis/blob/main/Analysis/Tools/ExistsUnique.lean)
-/
@[path]
private lemma main
  {p: α → Prop}
  {x : α}
-- given
  (h : ∃! x, p x)
  (hx : p x) :
-- imply
  h.choose = x :=
-- proof
  ExistsUnique.choose_eq h hx


-- created on 2026-10-20
