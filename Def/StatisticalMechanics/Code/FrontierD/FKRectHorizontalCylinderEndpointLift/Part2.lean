/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTwoPointComparison.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderEndpointLift
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

def fkRectHorizontalCylinderFixedEndpointDisplacement
    (height : Nat) : Site 2 :=
  fkRectHorizontalCylinderSquareLiftedDisplacement 0 height


def fkRectHorizontalCylinderReflectedDiagonalDisplacement
    (height : Nat) : Site 2 :=
  ![(height / 2 : Nat), -(height / 2 : Nat)]

end
end StatMech.FrontierD
