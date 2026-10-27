import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.RealERealENNReal


/--
[tsum_const_eq_top_of_pos](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  [Infinite α]
  {c : EReal}
-- given
  (hc : 0 < c) :
-- imply
  ∑' (_ : α), c = ⊤ :=
-- proof
  EReal.tsum_const_eq_top_of_pos hc


-- created on 2026-10-20
