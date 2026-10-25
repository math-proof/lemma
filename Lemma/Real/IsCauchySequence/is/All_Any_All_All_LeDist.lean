import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Sequence
open Chapter6.Sequence.IsCauchy


/--
[Sequence.IsCauchy.coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℝ} :
-- imply
  (a:Sequence).IsCauchy ↔ ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (a j) (a k) ≤ ε :=
-- proof
  Chapter6.Sequence.IsCauchy.coe a


-- created on 2026-10-22
