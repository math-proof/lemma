module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteVolume.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoundaryBridge.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open scoped BigOperators

open Filter Topology

open StatMech StatMech.Lattice StatMech.Ising StatMech.Percolation

noncomputable section

def oddRectangularPrismMeanNegEnergy
    (J beta : Real) (n : Nat) : Real :=
  (∑ sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n,
      Real.exp (-beta * rectangularPrismPlusEnergy J sigma) *
        (-rectangularPrismPlusEnergy J sigma)) /
    rectangularPrismPlusPartition J beta (2 * n + 1) (2 * n + 1) n


end
end StatMech.FrontierA
