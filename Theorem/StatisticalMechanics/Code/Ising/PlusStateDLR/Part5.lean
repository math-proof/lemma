/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Instance.StatisticalMechanics.Code.Ising.PlusStateDLR
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


theorem integral_bind_specApply (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (μ : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure μ]
    (f : ConfigSpace (Site d) →ᵇ ℝ) :
    ∫ y, f y ∂((isingSpecFull n B β h) ∘ₘ μ)
      = ∫ ω, specApply n B β h (f : ConfigSpace (Site d) → ℝ) ω ∂μ := by
  set K := isingSpecFull n B β h with hK
  
  have hbind : K ∘ₘ μ = (μ ⊗ₘ K).map Prod.snd := by
    rw [← Measure.snd_compProd μ K, Measure.snd]
  rw [hbind]
  rw [integral_map measurable_snd.aemeasurable
    (f.continuous.aestronglyMeasurable)]
  rw [Measure.integral_compProd]
  · refine integral_congr_ae (Eventually.of_forall (fun ω => ?_))
    show ∫ b, f b ∂(K ω) = specApply n B β h (f : ConfigSpace (Site d) → ℝ) ω
    rw [hK, isingSpecFull_apply]
    rfl
  · 
    exact (BoundedContinuousFunction.integrable (μ ⊗ₘ K) (f.compContinuous ⟨Prod.snd, continuous_snd⟩))


theorem psdlr_bind_eq (β h : ℝ) (hcons : FVConsistency d β h) (n : ℕ) :
    (isingSpecFull n (bondFinsetTouch d n) β h) ∘ₘ (plusState d β h : Measure (ConfigSpace (Site d)))
      = (plusState d β h : Measure (ConfigSpace (Site d))) := by
  set μ := (plusState d β h : Measure (ConfigSpace (Site d))) with hμ
  set K := isingSpecFull n (bondFinsetTouch d n) β h with hK
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  
  haveI : IsProbabilityMeasure (K ∘ₘ μ) := by
    rw [hK]; infer_instance
  
  have hfm : (⟨K ∘ₘ μ, inferInstance⟩ : FiniteMeasure (ConfigSpace (Site d)))
      = (⟨μ, inferInstance⟩ : FiniteMeasure (ConfigSpace (Site d))) := by
    refine FiniteMeasure.ext_of_forall_integral_eq (fun f => ?_)
    show ∫ y, f y ∂(K ∘ₘ μ) = ∫ y, f y ∂μ
    rw [integral_bind_specApply n (bondFinsetTouch d n) β h μ f]
    exact psdlr_specApply_integral_eq β h hcons n f
  have := congrArg (fun ν : FiniteMeasure (ConfigSpace (Site d)) => (ν : Measure (ConfigSpace (Site d)))) hfm
  simpa using this


end Ising
end StatMech
