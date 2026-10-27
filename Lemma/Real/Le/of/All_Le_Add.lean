import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.RealERealENNReal


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
