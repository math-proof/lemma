/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem boundaryTrace_abs_sub_le_of_lipschitz
    (Phi : Complex -> Complex) (L : NNReal)
    (hPhi : LipschitzWith L (fun z => (Phi z).im))
    (sample boundaryPoint : Complex) (value mesh : Real)
    (htrace : (Phi boundaryPoint).im = value)
    (hdist : dist sample boundaryPoint <= mesh) :
    |value - (Phi sample).im| <= L * mesh := by
  calc
    |value - (Phi sample).im| =
        dist (Phi sample).im (Phi boundaryPoint).im := by
      rw [Real.dist_eq, htrace, abs_sub_comm]
    _ <= L * dist sample boundaryPoint := hPhi.dist_le_mul sample boundaryPoint
    _ <= L * mesh := mul_le_mul_of_nonneg_left hdist L.2


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
