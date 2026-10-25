/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionRectangularModel.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteVolume.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDisorderGluing.Part4
import Theorem.StatisticalMechanics.Code.Ising.PressureSurfaceVolume.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoundaryBridge
open Filter Topology
open scoped symmDiff


namespace StatMech.FrontierA

noncomputable section

def HasPrismCubicalSurfaceComparison (beta : Real) : Prop :=
  Tendsto (fun n => rectangularPrismInterfaceDensity beta n -
    oddCubicalIsingDisorderDensity beta n) atTop (nhds 0)


def HasStandardPrismSurfaceComparison (beta : Real) : Prop :=
  Tendsto (fun n => standardCubicInterfaceDensity beta n -
    rectangularPrismInterfaceDensity beta n) atTop (nhds 0)


end
end StatMech.FrontierA
