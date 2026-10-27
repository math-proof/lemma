import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_6_6
open Chapter6
open Chapter6.Sequence


/--
[Sequence.convergent_of_subseq_of_bounded](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_6.lean)
-/
@[path]
private lemma main
  {a:ℕ→ ℝ}
-- given
  (ha: (a:Sequence).IsBounded) :
-- imply
  ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).Convergent :=
-- proof
  Chapter6.Sequence.convergent_of_subseq_of_bounded ha


-- created on 2026-10-22
