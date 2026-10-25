import Mathlib
import sympy.Basic
import Instance.Analysis.Section_11_1.Part8
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.Ioo_subset](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval} :
-- imply
  Ioo I.a I.b ⊆ I :=
-- proof
  Chapter11.BoundedInterval.Ioo_subset I


-- created on 2026-10-22
