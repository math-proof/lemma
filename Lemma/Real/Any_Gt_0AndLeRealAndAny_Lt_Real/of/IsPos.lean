import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.exists_rat_le_and_nat_gt](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {x:Chapter5.Real}
-- given
  (hx: x.IsPos) :
-- imply
  (∃ q:ℚ, q > 0 ∧ (q:Chapter5.Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Chapter5.Real) :=
-- proof
  Chapter5.Real.exists_rat_le_and_nat_gt hx


-- created on 2026-10-22
