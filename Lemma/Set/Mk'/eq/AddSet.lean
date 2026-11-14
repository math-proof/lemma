import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise


/--
[BoundedInterval.translate](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {c:ℝ} :
-- imply
  ((mk' (I.a + c) (I.b + c) I.lclosed I.uclosed : BoundedInterval) : Set ℝ)
    = (I:Set ℝ) + {c} :=
-- proof
  BoundedInterval.translate I c


-- created on 2026-10-22
