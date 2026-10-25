import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_1.Part9
open Chapter5


/--
[coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℚ} :
-- imply
  (a:Sequence).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (a j) (a k) ≤ ε :=
-- proof
  Chapter5.Sequence.IsCauchy.coe a


-- created on 2026-10-20
