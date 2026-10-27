import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.isNeg_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {x:Chapter5.Real} :
-- imply
  IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a :=
-- proof
  Chapter5.Real.isNeg_def x


-- created on 2026-10-22
