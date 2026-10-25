/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part2


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem exists_fderiv_im_norm_bound_on_compact
    (Phi : Complex -> Complex) (U K : Set Complex)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hPhi : AnalyticOnNhd Complex Phi U) :
    ∃ L : NNReal, forall w, w ∈ K ->
      ‖fderiv Real (fun z => (Phi z).im) w‖ ≤ L := by
  have hsmooth : ContDiffOn Real 1 (fun z => (Phi z).im) U :=
    contDiffOn_im_of_analyticOnNhd 1 Phi U hPhi
  have hcontinuous : ContinuousOn
      (fderiv Real (fun z => (Phi z).im)) K :=
    (hsmooth.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hKU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcontinuous
  let L : NNReal := ⟨max C 0, le_max_right C 0⟩
  refine ⟨L, fun w hw => (hC w hw).trans ?_⟩
  exact le_max_left C 0


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
