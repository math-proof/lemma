import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory Measure


/--
[absolutelyContinuous_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/AbsolutelyContinuous.lean)
-/
@[path]
lemma absolutelyContinuous_def
  {𝓕 : MeasurableSpace Ω}
  {μ ν : Measure Ω} :
-- imply
  ν ≪ μ ↔ ∀ A : Set Ω, μ A = 0 → ν A = 0 := by
-- proof
  constructor
  · intro h A hA
    exact h hA
  · intro h A hA
    exact h A hA


-- created on 2026-10-23
