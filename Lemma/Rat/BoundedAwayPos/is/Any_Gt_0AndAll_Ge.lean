import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real


/--
[boundedAwayPos_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℚ} :
-- imply
  BoundedAwayPos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c :=
-- proof
  Chapter5.boundedAwayPos_def a


-- created on 2026-10-22
