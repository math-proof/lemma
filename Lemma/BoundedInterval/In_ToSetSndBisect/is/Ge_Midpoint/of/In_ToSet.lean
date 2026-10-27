import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[mem_bisect_snd_iff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {I : BoundedInterval}
  {x : ℝ}
-- given
  (hx : x ∈ I.toSet) :
-- imply
  x ∈ (I.bisect.snd).toSet ↔ x ≥ I.midpoint :=
-- proof
  BoundedInterval.mem_bisect_snd_iff I x hx


-- created on 2026-10-22
