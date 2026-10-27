import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_11_1.Part8
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.set_Ico](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {a b:ℝ} :
-- imply
  (Ico a b : Set ℝ) = .Ico a b :=
-- proof
  Chapter11.BoundedInterval.set_Ico a b


-- created on 2026-10-22
