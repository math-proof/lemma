/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionUnconditionalBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderLimit.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionUnconditionalBounds
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

def cubicalInfiniteVolumeSquareWilsonDensity (K : Real) (n : Nat) : Real :=
  cubicalInfiniteVolumeWilsonFreeEnergy K
      (centralSquareSide n) (centralSquareSide n) /
    ((centralSquareSide n : Nat) : Real) ^ 2

end
end StatMech.FrontierA
