import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
open TaggedPartition


/--
[TaggedPartition.RiemannSum_changeTag_sub](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {n:ℕ}
  {P: TaggedPartition I n}
  {f: ℝ → ℝ}
  {k: Fin n}
  {t: ℝ}
-- given
  (ht: P.x k.castSucc ≤ t ∧ t ≤ P.x k.succ) :
-- imply
  (P.changeTag k t ht).RiemannSum f - P.RiemannSum f = (f t - f (P.x_tag k)) * P.delta k :=
-- proof
  TaggedPartition.RiemannSum_changeTag_sub P f k t ht


-- created on 2026-10-22
