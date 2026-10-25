/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Instance.StatisticalMechanics.Code.Foundations.CondDistribution.Part3
open MeasureTheory ProbabilityTheory MeasurableSpace


namespace StatMech

section ConfigSpace

variable {E : Type*} [Countable E]


theorem gibbsConditional_comp_trim
    (μ : Measure (ConfigSpace E)) [IsFiniteMeasure μ] (Λ : Set E) :
    gibbsConditional μ Λ ∘ₘ μ.trim (outsideSigma_le Λ) = μ := by
  unfold gibbsConditional
  exact regularCondDistrib_comp_trim μ (outsideSigma Λ) (outsideSigma_le Λ)


theorem gibbsConditional_compProd_trim
    (μ : Measure (ConfigSpace E)) [IsFiniteMeasure μ] (Λ : Set E) :
    (μ.trim (outsideSigma_le Λ)) ⊗ₘ (gibbsConditional μ Λ)
      = @Measure.map (ConfigSpace E) (ConfigSpace E × ConfigSpace E) _
          ((outsideSigma Λ).prod inferInstance) (fun ω ↦ (id ω, id ω)) μ := by
  unfold gibbsConditional
  exact regularCondDistrib_compProd_trim μ (outsideSigma Λ) (outsideSigma_le Λ)


theorem gibbsConditional_ae_eq_condExp
    (μ : Measure (ConfigSpace E)) [IsFiniteMeasure μ] (Λ : Set E)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s) :
    (fun ω ↦ ((gibbsConditional μ Λ) ω).real s) =ᵐ[μ] μ⟦s | outsideSigma Λ⟧ := by
  unfold gibbsConditional
  exact regularCondDistrib_ae_eq_condExp μ (outsideSigma Λ) (outsideSigma_le Λ) hs

end ConfigSpace
end StatMech
