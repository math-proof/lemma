/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIEquivalences.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.UniformIntegrable
open scoped MeasureTheory NNReal ENNReal
open MeasureTheory


namespace TheoryOfProbability3

variable {α : Type*} {ι : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- Textbook definition of uniform integrability of a family `f : ι → α → ℝ`:
each `f i` is `AEStronglyMeasurable` and for every `ε > 0` there is a uniform
truncation level `C : ℝ≥0` such that the `L¹` norm of the tail
`{x | C ≤ ‖f i x‖₊}.indicator (f i)` is at most `ε` for all `i`. This matches
Durrett's definition: `lim_{M→∞} sup_i E(|X_i|; |X_i| > M) = 0`. -/
def TextbookUniformlyIntegrable' (f : ι → α → ℝ) (μ : Measure α) : Prop :=
  (∀ i, AEStronglyMeasurable (f i) μ) ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ≥0, ∀ i, eLpNorm ({x | C ≤ ‖f i x‖₊}.indicator (f i)) 1 μ ≤ ENNReal.ofReal ε

end TheoryOfProbability3
