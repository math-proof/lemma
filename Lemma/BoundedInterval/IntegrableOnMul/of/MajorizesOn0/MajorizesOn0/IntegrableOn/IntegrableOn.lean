import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_4
open Chapter9
open Chapter11


/--
[integ_of_mul_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_4.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {f g:ℝ → ℝ}
-- given
  (hf: IntegrableOn f I)
  (hg: IntegrableOn g I)
  (hf_nonneg: MajorizesOn f 0 I)
  (hg_nonneg: MajorizesOn g 0 I) :
-- imply
  IntegrableOn (f * g) I :=
-- proof
  Chapter11.integ_of_mul_nonneg hf hg hf_nonneg hg_nonneg


-- created on 2026-10-22
