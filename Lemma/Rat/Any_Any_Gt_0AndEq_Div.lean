import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_6.Part2
open Chapter5 hiding Real
open Chapter5.Rat


/--
[Rat.eq_quot](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_6.lean)
-/
@[path]
private lemma main
  {q:ℚ} :
-- imply
  ∃ a:ℤ, ∃ b:ℕ, b > 0 ∧ q = a / b :=
-- proof
  Chapter5.Rat.eq_quot q


-- created on 2026-10-22
