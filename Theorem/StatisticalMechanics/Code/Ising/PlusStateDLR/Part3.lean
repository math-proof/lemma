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
import Def.StatisticalMechanics.Code.Ising.PlusStateDLR.Part3
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


theorem psdlr_specApply_integral_eq (β h : ℝ) (hcons : FVConsistency d β h)
    (n : ℕ) (f : ConfigSpace (Site d) →ᵇ ℝ) :
    ∫ ω, specApply n (bondFinsetTouch d n) β h (f : ConfigSpace (Site d) → ℝ) ω
        ∂(plusState d β h : Measure (ConfigSpace (Site d)))
      = ∫ ω, f ω ∂(plusState d β h : Measure (ConfigSpace (Site d))) := by
  obtain ⟨φ, hφ, hconv⟩ := plusState_isInfiniteVolumeState d β h
  
  set g := specApply_bcf n (bondFinsetTouch d n) β h f with hg
  
  have hLg : Tendsto (fun k => ∫ ω, g ω ∂((fun m => plusMeasure d m β h) (φ k) : Measure (ConfigSpace (Site d))))
      atTop (𝓝 (∫ ω, g ω ∂(plusState d β h : Measure (ConfigSpace (Site d))))) := by
    have := (hconv.tendsto_integral g)
    simpa [Function.comp] using this
  have hLf : Tendsto (fun k => ∫ ω, f ω ∂((fun m => plusMeasure d m β h) (φ k) : Measure (ConfigSpace (Site d))))
      atTop (𝓝 (∫ ω, f ω ∂(plusState d β h : Measure (ConfigSpace (Site d))))) := by
    have := (hconv.tendsto_integral f)
    simpa [Function.comp] using this
  
  have hev : ∀ᶠ k in atTop,
      (fun k => ∫ ω, g ω ∂((fun m => plusMeasure d m β h) (φ k) : Measure (ConfigSpace (Site d)))) k
        = (fun k => ∫ ω, f ω ∂((fun m => plusMeasure d m β h) (φ k) : Measure (ConfigSpace (Site d)))) k := by
    have hge : ∀ᶠ k in atTop, n ≤ φ k := by
      have : Tendsto φ atTop atTop := hφ.tendsto_atTop
      exact this.eventually_ge_atTop n
    filter_upwards [hge] with k hk
    simp only [hg, specApply_bcf_apply]
    exact hcons n (φ k) hk f
  
  have : (∫ ω, g ω ∂(plusState d β h : Measure (ConfigSpace (Site d))))
      = (∫ ω, f ω ∂(plusState d β h : Measure (ConfigSpace (Site d)))) :=
    tendsto_nhds_unique (hLg.congr' hev) hLf
  simpa only [hg, specApply_bcf_apply] using this


end Ising
end StatMech
