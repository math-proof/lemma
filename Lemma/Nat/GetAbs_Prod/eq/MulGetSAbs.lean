import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open Box


/--
[Box.volume_prod](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ}
  {B₁: Box d₁}
  {B₂: Box d₂} :
-- imply
  |(B₁.prod B₂)|ᵥ = |B₁|ᵥ * |B₂|ᵥ :=
-- proof
  Box.volume_prod B₁ B₂


-- created on 2026-10-22
