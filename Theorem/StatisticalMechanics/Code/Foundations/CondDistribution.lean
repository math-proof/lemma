/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Instance.StatisticalMechanics.Code.Foundations.CondDistribution
open MeasureTheory ProbabilityTheory MeasurableSpace


namespace StatMech

section SubSigma

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω)


theorem regularCondDistrib_comp_trim (hm : m ≤ mΩ) :
    (regularCondDistrib (mΩ := mΩ) μ m) ∘ₘ μ.trim hm = μ := by
  unfold regularCondDistrib
  exact condExpKernel_comp_trim (Ω := Ω) (m := m) (mΩ := mΩ) (μ := μ) hm


theorem regularCondDistrib_compProd_trim (hm : m ≤ mΩ) :
    (μ.trim hm) ⊗ₘ (regularCondDistrib (mΩ := mΩ) μ m)
      = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω ↦ (id ω, id ω)) μ := by
  unfold regularCondDistrib
  exact compProd_trim_condExpKernel (Ω := Ω) (m := m) (mΩ := mΩ) (μ := μ) hm


theorem condExp_ae_eq_integral_regularCondDistrib (hm : m ≤ mΩ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(regularCondDistrib (mΩ := mΩ) μ m) ω := by
  unfold regularCondDistrib
  exact condExp_ae_eq_integral_condExpKernel (Ω := Ω) (m := m) (mΩ := mΩ) (μ := μ) hm hf


theorem regularCondDistrib_ae_eq_condExp (hm : m ≤ mΩ)
    {s : Set Ω} (hs : @MeasurableSet Ω mΩ s) :
    (fun ω ↦ ((regularCondDistrib (mΩ := mΩ) μ m) ω).real s) =ᵐ[μ] μ⟦s | m⟧ := by
  unfold regularCondDistrib
  exact condExpKernel_ae_eq_condExp (Ω := Ω) (m := m) (mΩ := mΩ) (μ := μ) hm hs

end SubSigma
end StatMech
