import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real


/--
[bounded_away_zero_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℚ} :
-- imply
  BoundedAwayZero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c :=
-- proof
  Chapter5.bounded_away_zero_def a


-- created on 2026-10-22
