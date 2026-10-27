import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval


/--
[riemann_integral_eq_iff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {R:ℝ} :
-- imply
  riemann_integral_eq f I R ↔ ∀ ε>0, ∃ δ>0, ∀ n, ∀ P: TaggedPartition I n, P.norm ≤ δ → |P.RiemannSum f - R| ≤ ε :=
-- proof
  riemann_integral_eq_iff R


-- created on 2026-10-22
