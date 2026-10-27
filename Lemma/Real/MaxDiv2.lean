import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.RealERealENNReal


/--
[max_div_two](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {x : ℝ} :
-- imply
  max x 0 / 2 = max (x / 2) 0 :=
-- proof
  max_div_two x


-- created on 2026-10-20
