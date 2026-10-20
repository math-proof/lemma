import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_1
open Chapter5


/--
[ex_5_1_7_a](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  :
-- imply
  ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) :=
-- proof
  Chapter5.Sequence.ex_5_1_7_a


-- created on 2026-10-20
