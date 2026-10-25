/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateDecomposition


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexCanonicalOddBulkLogDisplacement
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  ∑ j, (sixVertexBetheLogObservable c
      (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) -
    sixVertexBetheLogObservable c
      (sixVertexCanonicalOddMidpointHalfRoot hc s k j))

def sixVertexCanonicalOddZeroModeWallisCorrection
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  Real.log (sixVertexZeroPhaseBethePrefactor c
      (sixVertexFourWidth (2 * s + 1) k)
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
      (sixVertexOddCentralIndex (s + k + 1))) - Real.log 2 +
    2 * ∑ j, (sixVertexBetheLogObservable c
        (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
      sixVertexBetheLogObservable c
        (sixVertexCanonicalOddLeftHalfRoot hc s k j))

def sixVertexCanonicalOddBoundaryLogSum
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  ∑ i, sixVertexBetheLogObservable c
    (sixVertexCanonicalOddBoundaryHalfRoot hc s k i)

end
end StatMech.FrontierD
