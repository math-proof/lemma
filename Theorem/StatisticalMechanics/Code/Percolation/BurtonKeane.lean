/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
open MeasureTheory

set_option linter.style.show false


namespace StatMech

namespace ConfigSpace

variable {E G : Type*} [Group G] [MulAction G E]

variable {μ : Measure (ConfigSpace E)}


theorem ergodic_ae_const_of_shiftInvariant [IsProbabilityMeasure μ]
    {β : Type*} [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (herg : IsErgodic (G := G) μ)
    (f : ConfigSpace E → β) (hf : Measurable f)
    (hinv : ∀ (g : G) (ω : ConfigSpace E), f (shift g ω) = f ω) :
    ∃ k : β, μ {ω | f ω = k} = 1 := by
  classical
  have hmeas : ∀ k : β, MeasurableSet {ω | f ω = k} := fun k =>
    hf (measurableSet_singleton k)
  have hshiftinv : ∀ k : β, ∀ g : G,
      (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' {ω | f ω = k} = {ω | f ω = k} := by
    intro k g
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hinv g ω]
  have hdich : ∀ k : β, μ {ω | f ω = k} = 0 ∨ μ {ω | f ω = k} = 1 := by
    intro k
    rcases herg.2 _ (hmeas k) (hshiftinv k) with h | h
    · exact Or.inl h
    · exact Or.inr (by rwa [measure_univ] at h)
  by_contra hcon
  simp only [not_exists] at hcon
  have hall0 : ∀ k : β, μ {ω | f ω = k} = 0 := by
    intro k
    rcases hdich k with h | h
    · exact h
    · exact absurd h (hcon k)
  have huniv : (Set.univ : Set (ConfigSpace E)) = ⋃ k : β, {ω | f ω = k} := by
    ext ω
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨f ω, rfl⟩
  have hz : μ Set.univ = 0 := by
    rw [huniv]
    refine le_antisymm ?_ zero_le'
    calc μ (⋃ k, {ω | f ω = k}) ≤ ∑' k, μ {ω | f ω = k} := measure_iUnion_le _
      _ = 0 := by simp [hall0]
  rw [measure_univ] at hz
  exact one_ne_zero hz

end ConfigSpace
end StatMech
