import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Pointwise
open Box


/--
[Box.measure_uniq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {T₁ T₂: Finset (Box d)}
-- given
  (hT₁: (T₁ : Set (Box d)).PairwiseDisjoint Box.toSet)
  (hT₂: (T₂ : Set (Box d)).PairwiseDisjoint Box.toSet)
  (heq: ⋃ B ∈ T₁, B.toSet = ⋃ B ∈ T₂, B.toSet) :
-- imply
  ∑ B ∈ T₁, |B|ᵥ = ∑ B ∈ T₂, |B|ᵥ :=
-- proof
  Box.measure_uniq hT₁ hT₂ heq


-- created on 2026-10-22
