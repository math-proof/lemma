import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open Box


/--
[Box.sample_finite](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {N:ℕ}
-- given
  (hN: N ≠ 0) :
-- imply
  Finite ↥(B.toSet ∩ (Set.range (fun (n:Fin d → ℤ) ↦ .toLp 2 (fun i ↦ (N:ℝ)⁻¹*(n i))))) :=
-- proof
  Box.sample_finite B hN


-- created on 2026-10-22
