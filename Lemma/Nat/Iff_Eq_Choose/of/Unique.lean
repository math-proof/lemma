import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Tools.ExistsUnique.Part2


/--
[choose_iff](https://github.com/teorth/analysis/blob/main/Analysis/Tools/ExistsUnique.lean)
-/
@[path]
private lemma main
  {p: α → Prop}
  {x : α}
-- given
  (h : ∃! x, p x) :
-- imply
  p x ↔ x = h.choose :=
-- proof
  ExistsUnique.choose_iff h x


-- created on 2026-10-20
