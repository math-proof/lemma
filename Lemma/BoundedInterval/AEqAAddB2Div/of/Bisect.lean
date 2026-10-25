import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[bisect_fst_eq_snd_shift](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {I₁ I₂ : BoundedInterval}
-- given
  (h : I₁.bisect.fst = I₂.bisect.snd) :
-- imply
  I₁.a = (I₂.a + I₂.b) / 2 :=
-- proof
  BoundedInterval.bisect_fst_eq_snd_shift h


-- created on 2026-10-22
