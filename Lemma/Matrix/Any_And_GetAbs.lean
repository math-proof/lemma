import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open Box


/--
[Box.volume_of_translate](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {x: EuclideanSpace' d} :
-- imply
  ∃ B' : Box d, B'.toSet = B.toSet + {x} ∧ |B'|ᵥ = |B|ᵥ :=
-- proof
  Box.volume_of_translate B x


-- created on 2026-10-22
