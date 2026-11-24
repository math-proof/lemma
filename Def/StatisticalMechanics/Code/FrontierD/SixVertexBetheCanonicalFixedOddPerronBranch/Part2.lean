module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargeContinuation.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddAnalyticCandidateSheet
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part2
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

noncomputable def sixVertexCanonicalFixedOddChargePerronBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin (((s + k + 1) + 1) + (s + k + 1)) → Real := by
  classical
  exact if h : ∃ p, SixVertexFixedOddChargePerronBranchWitness c s k p then
      Classical.choose h
    else
      sixVertexFixedOddChargeBetheRoots hc s k

end
end StatMech.FrontierD
