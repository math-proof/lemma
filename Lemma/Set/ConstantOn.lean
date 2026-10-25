import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_11_2.Part6
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.ConstantOn


/--
[ConstantOn.of_const'](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {c:ℝ}
  {X:Set ℝ} :
-- imply
  ConstantOn (fun _ ↦ c) X :=
-- proof
  Chapter11.ConstantOn.of_const' c X


-- created on 2026-10-22
