/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexCanonicalPerronBetheRoots
    {c : Real} (hc : 2 < c) (k : Nat) :
    Fin ((k + 1) + (k + 1)) → Real := by
  classical
  exact if h : ∃ p, SixVertexHalfFilledPerronBranchWitness c k p then
      Classical.choose h
    else
      sixVertexHalfFilledBetheRoots hc k

end
end StatMech.FrontierD
