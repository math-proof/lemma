/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IntegralDecayClose.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
open MeasureTheory Filter Topology BoundedContinuousFunction SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


theorem cdc_eventMassProb_reCfgIso_inv (σ : V ≃ W)
    (μV : ConfigSpace (Sym2 V) → ℝ) (μW : ConfigSpace (Sym2 W) → ℝ)
    (hμ : ∀ ω, μV (reCfgIso σ ω) = μW ω) (S : Set (ConfigSpace (Sym2 V))) :
    ∑ ω : ConfigSpace (Sym2 W),
          (reCfgIso σ ⁻¹' S).indicator (fun _ => (1:ℝ)) ω * μW ω
      = ∑ η : ConfigSpace (Sym2 V), S.indicator (fun _ => (1:ℝ)) η * μV η := by
  rw [← Equiv.sum_comp (reCfgIsoEquiv σ)
    (fun η => S.indicator (fun _ => (1:ℝ)) η * μV η)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  show (reCfgIso σ ⁻¹' S).indicator (fun _ => (1:ℝ)) ω * μW ω
    = S.indicator (fun _ => (1:ℝ)) (reCfgIso σ ω) * μV (reCfgIso σ ω)
  rw [hμ ω]
  have hind : (reCfgIso σ ⁻¹' S).indicator (fun _ => (1:ℝ)) ω
      = S.indicator (fun _ => (1:ℝ)) (reCfgIso σ ω) := by
    by_cases h : reCfgIso σ ω ∈ S
    · rw [Set.indicator_of_mem (show ω ∈ reCfgIso σ ⁻¹' S from h),
        Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (show ω ∉ reCfgIso σ ⁻¹' S from h),
        Set.indicator_of_notMem h]
  rw [hind]


end FK
end StatMech
