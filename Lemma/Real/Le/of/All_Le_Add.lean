import Mathlib
import sympy.Basic
import sympy.analysis.Misc.«Real-EReal-ENNReal»


/--
[le_of_forall_pos_le_add'](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {a b : EReal}
-- given
  (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ε) :
-- imply
  a ≤ b :=
-- proof
  EReal.le_of_forall_pos_le_add' h


-- created on 2026-10-20
