/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteVolume.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoundaryBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy


namespace StatMech.FrontierA

open scoped BigOperators

open Filter Topology

open StatMech StatMech.Lattice StatMech.Ising StatMech.Percolation

noncomputable section

def oddPrismPlusInteractionTerm (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    OddPrismTouchIndex n -> Real
  | .xInternal x y z =>
      rectangularPrismSpin sigma ⟨x.val, by omega⟩ y z *
        rectangularPrismSpin sigma ⟨x.val + 1, by omega⟩ y z
  | .yInternal x y z =>
      rectangularPrismSpin sigma x ⟨y.val, by omega⟩ z *
        rectangularPrismSpin sigma x ⟨y.val + 1, by omega⟩ z
  | .zInternal x y z =>
      rectangularPrismSpin sigma x y ⟨z.val, by omega⟩ *
        rectangularPrismSpin sigma x y ⟨z.val + 1, by omega⟩
  | .xZero y z => spin sigma ⟨0, y, z⟩
  | .xLast y z => spin sigma ⟨Fin.last (2 * n), y, z⟩
  | .yZero x z => spin sigma ⟨x, 0, z⟩
  | .yLast x z => spin sigma ⟨x, Fin.last (2 * n), z⟩
  | .zZero x y => spin sigma ⟨x, y, 0⟩
  | .zLast x y => spin sigma ⟨x, y, Fin.last (2 * n)⟩

end
end StatMech.FrontierA
