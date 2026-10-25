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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part3


namespace StatMech.FrontierA

open scoped BigOperators

open Filter Topology

open StatMech StatMech.Lattice StatMech.Ising StatMech.Percolation

noncomputable section

def oddPrismDobrushinInteractionTerm (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    OddPrismTouchIndex n -> Real
  | .xInternal x y z => oddPrismPlusInteractionTerm n sigma (.xInternal x y z)
  | .yInternal x y z => oddPrismPlusInteractionTerm n sigma (.yInternal x y z)
  | .zInternal x y z => oddPrismPlusInteractionTerm n sigma (.zInternal x y z)
  | .xZero y z => oddRectangularPrismDobrushinSign n z * spin sigma ⟨0, y, z⟩
  | .xLast y z => oddRectangularPrismDobrushinSign n z *
      spin sigma ⟨Fin.last (2 * n), y, z⟩
  | .yZero x z => oddRectangularPrismDobrushinSign n z * spin sigma ⟨x, 0, z⟩
  | .yLast x z => oddRectangularPrismDobrushinSign n z *
      spin sigma ⟨x, Fin.last (2 * n), z⟩
  | .zZero x y => oddRectangularPrismDobrushinSign n 0 * spin sigma ⟨x, y, 0⟩
  | .zLast x y => oddRectangularPrismDobrushinSign n (Fin.last (2 * n)) *
      spin sigma ⟨x, y, Fin.last (2 * n)⟩

end
end StatMech.FrontierA
