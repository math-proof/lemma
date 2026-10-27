import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Box


/--
[Box.mem_toSet](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {x : EuclideanSpace' d} :
-- imply
  x ∈ B.toSet ↔ ∀ i, x i ∈ (B.side i : Set ℝ) :=
-- proof
  Box.mem_toSet


-- created on 2026-10-22
