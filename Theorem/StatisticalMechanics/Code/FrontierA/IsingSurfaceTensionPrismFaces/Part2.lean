/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces.Part2


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech StatMech.Ising

noncomputable section

theorem rectangularPrismDobrushinBoundaryInteraction_eq_faces
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    (∑ v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n,
        oddRectangularPrismDobrushinSign n v.z *
          (rectangularPrismBoundaryDegree v : Real) * spin sigma v) =
      oddRectangularPrismDobrushinFaceInteraction n sigma := by
  simpa [oddRectangularPrismDobrushinFaceInteraction, mul_assoc,
    mul_left_comm, mul_comm] using
    sum_boundaryDegree_mul_eq_oddRectangularPrismFaceSum n
      (fun v => oddRectangularPrismDobrushinSign n v.z * spin sigma v)

end
end StatMech.FrontierA
