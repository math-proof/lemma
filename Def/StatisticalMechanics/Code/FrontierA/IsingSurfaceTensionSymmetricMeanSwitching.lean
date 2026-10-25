/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanBaseCases.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part35
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

def finiteExpVarianceSkewFourSummand
    {E : Type*} [Fintype E] (w I : E -> Real) (r : Real)
    (s : E × E × E × E) : Real :=
  w s.1 * w s.2.1 * w s.2.2.1 * w s.2.2.2 *
    (I s.1 - I s.2.1) ^ 2 *
      (Real.exp (r * (I s.1 + I s.2.1 - I s.2.2.1 - I s.2.2.2)) -
        Real.exp (-r *
          (I s.1 + I s.2.1 - I s.2.2.1 - I s.2.2.2)))


end
end StatMech.FrontierA
