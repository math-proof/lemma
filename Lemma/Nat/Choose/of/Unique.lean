import Mathlib
import sympy.Basic
import sympy.analysis.Tools.ExistsUnique


/--
[choose_spec](https://github.com/teorth/analysis/blob/main/Analysis/Tools/ExistsUnique.lean)
-/
@[path]
private lemma main
  {p: α → Prop}
-- given
  (h : ∃! x, p x) :
-- imply
  p h.choose :=
-- proof
  ExistsUnique.choose_spec h


-- created on 2026-10-20
