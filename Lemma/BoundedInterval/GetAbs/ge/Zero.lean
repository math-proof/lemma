import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_1
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.length_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval} :
-- imply
  0 ≤ |I|ₗ :=
-- proof
  Chapter11.BoundedInterval.length_nonneg I


-- created on 2026-10-22
