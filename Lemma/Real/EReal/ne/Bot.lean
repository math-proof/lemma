import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_2
open EReal


/--
[EReal.real_neq_neg_infty](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_2.lean)
-/
@[path]
private lemma main
  {x:ℝ} :
-- imply
  (x:EReal) ≠ ⊥ :=
-- proof
  EReal.real_neq_neg_infty x


-- created on 2026-10-22
