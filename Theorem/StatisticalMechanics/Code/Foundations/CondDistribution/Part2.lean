/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Instance.StatisticalMechanics.Code.Foundations.CondDistribution.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace


namespace StatMech

section Map

variable {Ω β : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [mβ : MeasurableSpace β] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → β)


theorem condDistribGiven_disintegrate :
    (μ.map X) ⊗ₘ condDistribGiven μ X = μ.map fun a ↦ (X a, a) := by
  unfold condDistribGiven
  exact compProd_map_condDistrib (Y := id) (X := X) (μ := μ) (mβ := mβ) aemeasurable_id


theorem condDistribGiven_comp (hX : AEMeasurable X μ) :
    condDistribGiven μ X ∘ₘ (μ.map X) = μ := by
  unfold condDistribGiven
  have h := condDistrib_comp_map (Y := (id : Ω → Ω)) (X := X) (μ := μ) hX aemeasurable_id
  rwa [Measure.map_id] at h


theorem condDistribGiven_ae_eq_condExp (hX : Measurable X) {s : Set Ω} (hs : MeasurableSet s) :
    (fun a ↦ (condDistribGiven μ X (X a)).real s) =ᵐ[μ] μ⟦s | mβ.comap X⟧ := by
  unfold condDistribGiven
  have h := condDistrib_ae_eq_condExp (Y := (id : Ω → Ω)) (X := X) (μ := μ) hX measurable_id hs
  simpa using h

end Map


section ConfigSpace

variable {E : Type*} [Countable E]


example : StandardBorelSpace (ConfigSpace E) := inferInstance


end ConfigSpace
end StatMech
