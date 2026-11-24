module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisBridge.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisFixed.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddAveragedDensityEndpoints
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisLimit


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexCanonicalOddAveragedHalfIncrementSum
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  2 * ∑ j : Fin (s + k + 1),
    (Real.log (sixVertexCanonicalOddCountingAverage hc s k
        (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
      Real.log (sixVertexCanonicalOddCountingAverage hc s k
        (sixVertexCanonicalOddLeftHalfRoot hc s k j)))

end
end StatMech.FrontierD
