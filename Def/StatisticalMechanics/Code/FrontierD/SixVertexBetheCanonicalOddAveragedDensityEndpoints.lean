/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensityEndpoints.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddAveragedDensity
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisFixed.Part3


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexCanonicalOddCountingAverage
    {c : Real} (hc : 2 < c) (s k : Nat) (x : Real) : Real :=
  sixVertexBetheCountingFunction c
      (sixVertexFourWidth (2 * s + 1) k)
      ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
      (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x / x

end
end StatMech.FrontierD
