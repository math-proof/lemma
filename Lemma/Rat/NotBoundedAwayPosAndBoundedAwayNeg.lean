import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real


/--
[not_boundedAwayPos_boundedAwayNeg](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℚ} :
-- imply
  ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) :=
-- proof
  Chapter5.not_boundedAwayPos_boundedAwayNeg


-- created on 2026-10-22
