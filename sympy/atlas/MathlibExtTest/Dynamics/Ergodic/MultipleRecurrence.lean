/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Dynamics/Ergodic/MultipleRecurrence.lean -/


import sympy.atlas.Dynamics.Ergodic.MultipleRecurrence
import Lemma.Set.Ergodic.MultipleRecurrence

import Mathlib.Tactic


open MeasureTheory
open MathlibExt.Dynamics.Ergodic.MultipleRecurrenceWanted

namespace MathlibExtTest.Dynamics.Ergodic.MultipleRecurrence

-- The two-term case gives Poincaré recurrence.
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    {A : Set α} (hA : MeasurableSet A) (hApos : 0 < μ A) :
    ∃ n : ℕ, 0 < n ∧ 0 < μ (A ∩ T^[n] ⁻¹' A) := by
  obtain ⟨n, hn, hpos⟩ := furstenberg_multipleRecurrence hT hA hApos 2 (by omega)
  refine ⟨n, hn, ?_⟩
  have hrange : Finset.range 2 = {0, 1} := by decide
  rw [hrange] at hpos
  simpa using hpos

-- The three-term case supplies a point with two recurrent iterates.
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    {A : Set α} (hA : MeasurableSet A) (hApos : 0 < μ A) :
    ∃ n : ℕ, 0 < n ∧ ∃ x ∈ A, T^[n] x ∈ A ∧ T^[2 * n] x ∈ A := by
  obtain ⟨n, hn, hpos⟩ := furstenberg_multipleRecurrence hT hA hApos 3 (by omega)
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (ne_of_gt hpos)
  refine ⟨n, hn, x, ?_⟩
  have hrange : Finset.range 3 = {0, 1, 2} := by decide
  rw [hrange] at hx
  simpa using hx

end MathlibExtTest.Dynamics.Ergodic.MultipleRecurrence
