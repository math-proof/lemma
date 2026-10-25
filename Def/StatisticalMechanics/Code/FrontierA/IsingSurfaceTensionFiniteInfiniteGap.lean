/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteInfiniteGap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionUnconditionalBounds.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSurfaceTensionIdentification
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteInfiniteGap
open Filter Topology


namespace StatMech.FrontierA

noncomputable section

def cubicalFiniteInfiniteSquareDensityGap (K : Real) (n : Nat) : Real :=
  cubicalSquareWilsonDensity K n -
    cubicalInfiniteVolumeSquareWilsonDensity K n

end
end StatMech.FrontierA
