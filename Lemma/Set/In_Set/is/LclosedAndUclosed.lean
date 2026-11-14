import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[BoundedInterval.mem_iff'](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {x:ℝ} :
-- imply
  x ∈ (I:Set ℝ) ↔
      ((if I.lclosed then I.a ≤ x else I.a < x) ∧ (if I.uclosed then x ≤ I.b else x < I.b)) :=
-- proof
  BoundedInterval.mem_iff' I x


-- created on 2026-10-22
