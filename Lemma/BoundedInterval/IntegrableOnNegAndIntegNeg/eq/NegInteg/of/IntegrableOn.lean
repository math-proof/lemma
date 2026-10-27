import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_11_4
open Chapter9
open Chapter11
open Chapter11.IntegrableOn


/--
[IntegrableOn.neg](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_4.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {f:ℝ → ℝ}
-- given
  (hf: IntegrableOn f I) :
-- imply
  IntegrableOn (-f) I ∧ integ (-f) I = -integ f I :=
-- proof
  Chapter11.IntegrableOn.neg hf


-- created on 2026-10-22
