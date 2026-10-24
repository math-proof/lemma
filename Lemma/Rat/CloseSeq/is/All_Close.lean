import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_2
open Chapter5
open Chapter5.Rat


/--
[Rat.closeSeq_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_2.lean)
-/
@[path]
private lemma main
  {ε: ℚ}
  {a b: Sequence} :
-- imply
  ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) :=
-- proof
  Chapter5.Rat.closeSeq_def ε a b


-- created on 2026-10-22
