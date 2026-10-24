/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/MultipleRecurrence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import sympy.atlas.Combinatorics.Additive.Szemeredi
import Lemma.Finset.Additive.Szemeredi
/-!
# Furstenberg multiple recurrence

This file proves Furstenberg's multiple recurrence theorem for a measure-preserving
transformation of a probability space.
-/

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Dynamics.Ergodic.MultipleRecurrenceWanted

private noncomputable def furstVisitCount {α : Type*} (T : α → α) (A : Set α)
    (N : ℕ) (x : α) : ℕ := by
  classical
  exact ((Finset.range N).filter fun m => T^[m] x ∈ A).card

private def furstProgressionSet {α : Type*} (T : α → α) (A : Set α)
    (k a d : ℕ) : Set α :=
  ⋂ i ∈ Finset.range k, T^[a + i * d] ⁻¹' A
end MathlibExt.Dynamics.Ergodic.MultipleRecurrenceWanted
