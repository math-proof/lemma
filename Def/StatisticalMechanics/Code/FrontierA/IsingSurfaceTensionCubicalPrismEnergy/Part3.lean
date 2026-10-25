/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetGauge
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCubicalPrismEnergy.Part2


namespace StatMech.FrontierA

open scoped BigOperators symmDiff

open Filter Topology

open StatMech StatMech.Ising

noncomputable section

def oddCubicalPlaquetteEquivOddPrismTouchIndex (n : Nat) :
    CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) ≃
      OddPrismTouchIndex n where
  toFun := cubicalPlaquetteToOddPrism n
  invFun := oddPrismToCubicalPlaquette n
  left_inv := cubicalPlaquetteToOddPrism_leftInverse n
  right_inv := cubicalPlaquetteToOddPrism_rightInverse n

end
end StatMech.FrontierA
