module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargeContinuation.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddAnalyticCandidateSheet
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part3
open Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOddPerronBranch.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalFixedOddChargeBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  sixVertexZeroPhaseBetheEigenvalueValue c
    (sixVertexFourWidth (2 * s + 1) k)
    (sixVertexCanonicalFixedOddChargePerronBetheRoots hc s k)
    (sixVertexOddCentralIndex (s + k + 1))

end
end StatMech.FrontierD
