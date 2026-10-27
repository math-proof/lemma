import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_11_4
open Chapter9
open Chapter11


/--
[integ_of_mul](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_4.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {f g:ℝ → ℝ}
-- given
  (hf: IntegrableOn f I)
  (hg: IntegrableOn g I) :
-- imply
  IntegrableOn (f * g) I :=
-- proof
  Chapter11.integ_of_mul hf hg


-- created on 2026-10-22
