import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
@[path]
private lemma main
  {I : BoundedInterval}
  {x : ℝ}
-- given
  (hx : x ∈ I.toSet) :
-- imply
  x ∈ (I.bisect.fst).toSet ↔ x ≤ I.midpoint :=
-- proof
  BoundedInterval.mem_bisect_fst_iff I x hx


-- created on 2026-10-22
