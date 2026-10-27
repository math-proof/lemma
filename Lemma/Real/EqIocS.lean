import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_11_1.Part8
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.set_Ioc](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {a b:ℝ} :
-- imply
  (Ioc a b : Set ℝ) = .Ioc a b :=
-- proof
  Chapter11.BoundedInterval.set_Ioc a b


-- created on 2026-10-22
