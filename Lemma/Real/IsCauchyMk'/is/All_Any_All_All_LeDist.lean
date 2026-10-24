import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_1
open Chapter6
open Chapter6.Sequence
open Chapter6.Sequence.IsCauchy


/--
[Sequence.IsCauchy.mk](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {n₀:ℤ}
  {a: {n // n ≥ n₀} → ℝ} :
-- imply
  (mk' n₀ a).IsCauchy
  ↔ ∀ ε > 0, ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N, dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε :=
-- proof
  Chapter6.Sequence.IsCauchy.mk a


-- created on 2026-10-22
