import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open Box


/--
[Box.translate](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {x: EuclideanSpace' d} :
-- imply
  ∃ B' : Box d, (B':Set (EuclideanSpace' d)) = (B:Set (EuclideanSpace' d)) + {x} :=
-- proof
  Box.translate B x


-- created on 2026-10-22
