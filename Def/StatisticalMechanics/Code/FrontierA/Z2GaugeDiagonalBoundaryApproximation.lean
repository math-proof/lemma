/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDiagonalBoundaryApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionUnconditionalBounds.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDiagonalBoundaryApproximation
open Filter Topology


namespace StatMech.FrontierA

noncomputable section

noncomputable def cubicalDiagonalApproximationPadding
    {K : Real} (hK : 0 < K) (n : Nat) : Nat :=
  Classical.choose
    (exists_cubicalPaddedDisorderDensity_close_infiniteVolume hK n
      (by positivity :
        0 < (1 : Real) / ((centralSquareSide n : Nat) : Real)))


def cubicalDiagonalFiniteInfiniteDensityGap
    {K : Real} (hK : 0 < K) (n : Nat) : Real :=
  let m := cubicalDiagonalApproximationPadding hK n
  cubicalPaddedDisorderFreeEnergy K
        (centralSquareSide n) (centralSquareSide n) m m m m m m /
      ((centralSquareSide n : Nat) : Real) ^ 2 -
    cubicalInfiniteVolumeSquareWilsonDensity K n

end
end StatMech.FrontierA
