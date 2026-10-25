import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_2.Part2
open Chapter5
open Chapter5.Sequence


/--
[Sequence.equiv_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_2.lean)
-/
@[path]
private lemma main
  {a b: ℕ → ℚ} :
-- imply
  Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (a:Sequence) (b:Sequence) :=
-- proof
  Chapter5.Sequence.equiv_def a b


-- created on 2026-10-22
