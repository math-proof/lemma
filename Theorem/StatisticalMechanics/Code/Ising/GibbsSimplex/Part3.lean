/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Ising.DLR
import Instance.StatisticalMechanics.Code.Ising.GibbsSimplex
open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped BigOperators ENNReal

set_option linter.style.longLine false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


theorem gibbsConditional_ae_eq_isingSpec (β h : ℝ)
    (μ : Measure (ConfigSpace (Site d))) [IsFiniteMeasure μ]
    (hμ : IsDLRState d β h μ) (n : ℕ) :
    gibbsConditional μ (box d n) =ᵐ[μ] isingSpec n (bondFinsetTouch d n) β h := by
  filter_upwards [hμ n] with η hη
  rw [hη, isingSpec_apply]


theorem dlr_compProd_trim_eq (β h : ℝ)
    (μ : Measure (ConfigSpace (Site d))) [IsFiniteMeasure μ]
    (hμ : IsDLRState d β h μ) (n : ℕ) :
    (μ.trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h)
      = @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _
          ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω)) μ := by
  have htrim : gibbsConditional μ (box d n)
      =ᵐ[μ.trim (outsideSigma_le (box d n))] isingSpec n (bondFinsetTouch d n) β h := by
    refine kernel_ae_eq_trim inferInstance (outsideSigma (box d n)) (outsideSigma_le (box d n))
      _ _ μ ?_ ?_ (gibbsConditional_ae_eq_isingSpec β h μ hμ n)
    · intro η
      exact (isMarkovKernel_gibbsConditional μ (box d n)).isProbabilityMeasure η
    · intro η
      exact (isMarkov_isingSpec n (bondFinsetTouch d n) β h).isProbabilityMeasure η
  rw [← gibbsConditional_compProd_trim μ (box d n)]
  exact (Measure.compProd_congr htrim).symm


theorem isDLRState_of_compProd_trim (β h : ℝ)
    (μ : Measure (ConfigSpace (Site d))) [IsFiniteMeasure μ]
    (hμ : ∀ n, (μ.trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h)
      = @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _
          ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω)) μ) :
    IsDLRState d β h μ := by
  intro n
  
  have hcompProd :
      (μ.trim (outsideSigma_le (box d n))) ⊗ₘ (gibbsConditional μ (box d n))
        = (μ.trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h) := by
    rw [gibbsConditional_compProd_trim μ (box d n), hμ n]
  
  have htrim : gibbsConditional μ (box d n)
      =ᵐ[μ.trim (outsideSigma_le (box d n))] isingSpec n (bondFinsetTouch d n) β h :=
    Kernel.ae_eq_of_compProd_eq hcompProd
  
  have hμae : gibbsConditional μ (box d n) =ᵐ[μ] isingSpec n (bondFinsetTouch d n) β h :=
    ae_of_ae_trim (outsideSigma_le (box d n)) htrim
  filter_upwards [hμae] with η hη
  rw [hη, isingSpec_apply]


theorem isDLRState_add_smul (β h : ℝ) {a b : ℝ≥0∞} (hab : a + b = 1)
    (μ₁ μ₂ : Measure (ConfigSpace (Site d))) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h₁ : IsDLRState d β h μ₁) (h₂ : IsDLRState d β h μ₂) :
    haveI : IsFiniteMeasure (a • μ₁ + b • μ₂) := by
      have ha : a ≠ ∞ := by rintro rfl; simp at hab
      have hb : b ≠ ∞ := by rintro rfl; rw [add_top] at hab; simp at hab
      haveI := μ₁.smul_finite ha
      haveI := μ₂.smul_finite hb
      infer_instance
    IsDLRState d β h (a • μ₁ + b • μ₂) := by
  have ha : a ≠ ∞ := by rintro rfl; simp at hab
  have hb : b ≠ ∞ := by rintro rfl; rw [add_top] at hab; simp at hab
  haveI : IsFiniteMeasure (a • μ₁) := μ₁.smul_finite ha
  haveI : IsFiniteMeasure (b • μ₂) := μ₂.smul_finite hb
  haveI : IsFiniteMeasure (a • μ₁ + b • μ₂) := inferInstance
  refine isDLRState_of_compProd_trim β h _ (fun n => ?_)
  set hm := outsideSigma_le (box d n) with hmdef
  set K := isingSpec n (bondFinsetTouch d n) β h with hKdef
  set f : ConfigSpace (Site d) → ConfigSpace (Site d) × ConfigSpace (Site d) :=
    fun ω => (id ω, id ω) with hfdef
  have hf : @Measurable (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d))
      _ ((outsideSigma (box d n)).prod inferInstance) f := by
    rw [hfdef]
    exact (measurable_id'' hm).prodMk measurable_id
  
  have e₁ := dlr_compProd_trim_eq β h μ₁ h₁ n
  have e₂ := dlr_compProd_trim_eq β h μ₂ h₂ n
  
  have hLHS : ((a • μ₁ + b • μ₂).trim hm) ⊗ₘ K
      = a • ((μ₁.trim hm) ⊗ₘ K) + b • ((μ₂.trim hm) ⊗ₘ K) := by
    rw [trim_add hm, trim_smul μ₁ hm a, trim_smul μ₂ hm b,
      Measure.compProd_add_left, Measure.compProd_smul_left, Measure.compProd_smul_left]
  
  have hRHS : @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _
        ((outsideSigma (box d n)).prod inferInstance) f (a • μ₁ + b • μ₂)
      = a • (@Measure.map _ _ _ ((outsideSigma (box d n)).prod inferInstance) f μ₁)
        + b • (@Measure.map _ _ _ ((outsideSigma (box d n)).prod inferInstance) f μ₂) := by
    rw [Measure.map_add _ _ hf, Measure.map_smul, Measure.map_smul]
  rw [hLHS, hRHS, e₁, e₂]


theorem convex_isDLRState (β h : ℝ) {a b : ℝ≥0∞} (hab : a + b = 1)
    (μ₁ μ₂ : Measure (ConfigSpace (Site d))) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure (a • μ₁ + b • μ₂)]
    (h₁ : IsDLRState d β h μ₁) (h₂ : IsDLRState d β h μ₂) :
    IsDLRState d β h (a • μ₁ + b • μ₂) :=
  isDLRState_add_smul β h hab μ₁ μ₂ h₁ h₂

end Ising
end StatMech
