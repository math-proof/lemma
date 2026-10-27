import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_9_10
open Chapter9


/--
[iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_10.lean)
-/
@[path]
private lemma main
  {X: Set ℝ}
  {f:ℝ → ℝ}
  {L:ℝ} :
-- imply
  Filter.Tendsto f (.atTop ⊓ .principal X) (nhds L) ↔ ∀ ε > (0:ℝ), ∃ M, ∀ x ∈ X ∩ .Ici M, |f x - L| < ε :=
-- proof
  Chapter9.Filter.Tendsto.AtTop.iff f L


-- created on 2026-10-20
