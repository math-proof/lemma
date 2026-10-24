import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_3
open BoundedInterval
open TaggedPartition


/--
[TaggedPartition.exists_norm_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {δ : ℝ}
-- given
  (hI: I = Icc I.a I.b)
  (hab: I.a < I.b)
  (hδ : 0 < δ) :
-- imply
  ∃ (n : ℕ) (P : TaggedPartition I n), P.norm ≤ δ :=
-- proof
  TaggedPartition.exists_norm_le I hI hab δ hδ


-- created on 2026-10-22
