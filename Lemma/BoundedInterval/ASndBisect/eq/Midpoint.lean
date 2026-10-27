import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[bisect_snd_a](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {I : BoundedInterval} :
-- imply
  (I.bisect.snd).a = I.midpoint :=
-- proof
  BoundedInterval.bisect_snd_a I


-- created on 2026-10-22
