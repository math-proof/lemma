/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.KingmanFilling.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.AnimalLLNas.Part3
open MeasureTheory Filter Topology Finset
open StatMech.Kingman StatMech.KingmanAE StatMech.KingmanFilling


namespace StatMech

namespace BeffaraDC

variable {ρ : Measure ℝ}


theorem animalLimit_integrable [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ) :
    Integrable (animalLimit ρ) (Measure.infinitePi (fun _ : ℤ => ρ)) :=
  integrable_kingmanLimit (animalCocycle hρ) (fun n => animalValue_nonneg_ae n)


theorem animalLimit_nonneg_ae [IsProbabilityMeasure ρ] :
    0 ≤ᵐ[Measure.infinitePi (fun _ : ℤ => ρ)] animalLimit ρ :=
  kingmanLimit_nonneg_ae (T := shiftEnv) (fun n => animalValue_nonneg_ae n)


theorem animalLimit_shift_invariant_ae [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)),
      animalLimit ρ (shiftEnv ω) = animalLimit ρ ω := by
  have hcoc := animalCocycle hρ
  have hnn : ∀ n, 0 ≤ᵐ[Measure.infinitePi (fun _ : ℤ => ρ)] (fun ω => animalValue ω n) :=
    fun n => animalValue_nonneg_ae n
  exact kingmanLimit_comp_ae hcoc (gStar_le_gStarLow_ae hcoc hnn)
    (by filter_upwards [gStar_nonneg_ae (T := shiftEnv) hnn] with ω hω using
      lt_of_lt_of_le EReal.bot_lt_zero hω)
    (animalLimit_integrable hρ)


theorem integral_animalLimit_le [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ) :
    (∫ ω, animalLimit ρ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)))
      ≤ SubadditiveCocycle.gamma (animalCocycle hρ) :=
  integral_kingmanLimit_le_gamma (animalCocycle hρ) (fun n => animalValue_nonneg_ae n)


theorem integral_animalLimit_eq_gamma [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ) :
    (∫ ω, animalLimit ρ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)))
      = SubadditiveCocycle.gamma (animalCocycle hρ) := by
  have hcoc := animalCocycle hρ
  have hnn : ∀ n, 0 ≤ᵐ[Measure.infinitePi (fun _ : ℤ => ρ)] (fun ω => animalValue ω n) :=
    fun n => animalValue_nonneg_ae n
  refine le_antisymm (integral_animalLimit_le hρ) ?_
  
  have hgamma_le : hcoc.gamma ≤ ∫ ω, gLow shiftEnv (fun n ω => animalValue ω n) ω
      ∂(Measure.infinitePi (fun _ : ℤ => ρ)) :=
    gamma_le_integral_gLow hcoc hnn
  have heq : (∫ ω, gLow shiftEnv (fun n ω => animalValue ω n) ω
        ∂(Measure.infinitePi (fun _ : ℤ => ρ)))
      = ∫ ω, animalLimit ρ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)) := by
    refine integral_congr_ae ?_
    filter_upwards [gStar_le_gStarLow_ae hcoc hnn] with ω h1
    have hle : gStarLow shiftEnv (fun n ω => animalValue ω n) ω
        = gStar shiftEnv (fun n ω => animalValue ω n) ω :=
      le_antisymm (gStarLow_le_gStar (T := shiftEnv) ω) h1
    simp only [animalLimit, kingmanLimit, gLow, hle]
  linarith [hgamma_le, heq.le, heq.ge]


theorem animalValue_eq_directed_window (ω : ℤ → ℝ) (n : ℕ) :
    animalValue ω n
      = (range (n + 1)).sup' (by simp) (fun a => ∑ i ∈ range a, ω (i : ℤ)) := rfl

end BeffaraDC
end StatMech
