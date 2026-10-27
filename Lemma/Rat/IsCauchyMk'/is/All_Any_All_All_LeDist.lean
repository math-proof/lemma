import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_1.Part9
open Chapter5
open Chapter5.Sequence
open Chapter5.Sequence.IsCauchy


/--
[Sequence.IsCauchy.mk](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {n₀:ℤ}
  {a: {n // n ≥ n₀} → ℚ} :
-- imply
  (mk' n₀ a).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N,
  Section_4_3.dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε :=
-- proof
  Chapter5.Sequence.IsCauchy.mk a


-- created on 2026-10-22
