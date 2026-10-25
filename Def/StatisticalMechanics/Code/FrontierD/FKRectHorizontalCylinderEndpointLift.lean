/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTwoPointComparison.Part4
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

def fkRectHorizontalCylinderSquareLiftedDisplacement
    (dx : Int) (height : Nat) : Site 2 :=
  ![dx + (height / 2 : Nat), dx - (height / 2 : Nat) + 1]


end
end StatMech.FrontierD
