/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTwoPointComparison.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderEndpointLift.Part2
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

theorem fkRectHorizontalCylinder_fixedEndpoint_sub_reflectedDiagonal
    (R : FKRectTorus) :
    fkRectHorizontalCylinderFixedEndpointDisplacement R.height -
        fkRectHorizontalCylinderReflectedDiagonalDisplacement R.height =
      ![0, 1] := by
  funext i
  fin_cases i <;>
    simp [fkRectHorizontalCylinderFixedEndpointDisplacement,
      fkRectHorizontalCylinderSquareLiftedDisplacement,
      fkRectHorizontalCylinderReflectedDiagonalDisplacement]


end
end StatMech.FrontierD
