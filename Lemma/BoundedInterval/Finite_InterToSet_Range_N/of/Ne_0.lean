import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise


/--
[BoundedInterval.sample_finite](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I : BoundedInterval}
  {N:ℕ}
-- given
  (hN: N ≠ 0) :
-- imply
  Finite ↥(I.toSet ∩ (Set.range (fun n:ℤ ↦ (N:ℝ)⁻¹*n))) :=
-- proof
  BoundedInterval.sample_finite I hN


-- created on 2026-10-22
