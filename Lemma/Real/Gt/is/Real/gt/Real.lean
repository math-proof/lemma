import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.gt_of_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {q q':ℚ} :
-- imply
  q > q' ↔ (q:Chapter5.Real) > (q':Chapter5.Real) :=
-- proof
  Chapter5.Real.gt_of_coe q q'


-- created on 2026-10-22
