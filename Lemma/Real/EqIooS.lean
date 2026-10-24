import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_1
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.set_Ioo](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {a b:ℝ} :
-- imply
  (Ioo a b : Set ℝ) = .Ioo a b :=
-- proof
  Chapter11.BoundedInterval.set_Ioo a b


-- created on 2026-10-22
