import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.RealERealENNReal


/--
[tsum_add_coe_ennreal](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {a b : α → ENNReal} :
-- imply
  (∑' n, ↑(a n) : EReal) + (∑' n, ↑(b n) : EReal) = (∑' n, ↑(a n + b n) : EReal) :=
-- proof
  EReal.tsum_add_coe_ennreal


-- created on 2026-10-20
