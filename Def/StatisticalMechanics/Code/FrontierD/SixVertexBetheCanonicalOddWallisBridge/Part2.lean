/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisCore.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisBridge.Part2


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexCanonicalOddWallisProductRatio
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  sixVertexCanonicalOddActualHalfProduct hc s k /
    sixVertexOddWallisHalfProduct (s + k + 1)


def SixVertexCanonicalOddGeneralizedWallisComparison
    {c : Real} (hc : 2 < c) (s : Nat) : Prop :=
  Tendsto (fun k => sixVertexCanonicalOddWallisProductRatio hc s k ^ 2)
    atTop (nhds
      (Real.cosh (sixVertexAntiferroelectricLambda c) /
        (4 * c ^ 2 * sixVertexFourierPhysicalDensity c hc 0)))

def sixVertexCanonicalOddSmoothWallisLog
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  2 * ∑ j : Fin (s + k + 1),
    ((sixVertexBetheLogObservable c
          (sixVertexCanonicalOddMidpointHalfRoot hc s k j) +
        Real.log (sixVertexBetheCountingFunction c N n p
          (sixVertexCanonicalOddMidpointHalfRoot hc s k j))) -
      (sixVertexBetheLogObservable c
          (sixVertexCanonicalOddLeftHalfRoot hc s k j) +
        Real.log (sixVertexBetheCountingFunction c N n p
          (sixVertexCanonicalOddLeftHalfRoot hc s k j))))

def SixVertexCanonicalOddSmoothWallisLimit
    {c : Real} (hc : 2 < c) (s : Nat) : Prop :=
  Tendsto (sixVertexCanonicalOddSmoothWallisLog hc s) atTop
    (nhds (Real.log
      (Real.cosh (sixVertexAntiferroelectricLambda c) /
        (4 * c ^ 2 * sixVertexFourierPhysicalDensity c hc 0))))

end
end StatMech.FrontierD
