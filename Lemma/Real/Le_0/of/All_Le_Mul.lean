import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_11_4
open Chapter9
open Chapter11


/--
[nonneg_of_le_const_mul_eps](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_4.lean)
-/
@[path]
private lemma main
  {x C:ℝ}
-- given
  (h: ∀ ε>0, x ≤ C * ε) :
-- imply
  x ≤ 0 :=
-- proof
  Chapter11.nonneg_of_le_const_mul_eps h


-- created on 2026-10-22
