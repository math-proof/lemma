import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_3
open Chapter5 hiding Real


/--
[LIM_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℚ}
-- given
  (ha: (a:Sequence).IsCauchy) :
-- imply
  LIM a = Quotient.mk _ (CauchySequence.mk' ha) :=
-- proof
  Chapter5.LIM_def ha


-- created on 2026-10-22
