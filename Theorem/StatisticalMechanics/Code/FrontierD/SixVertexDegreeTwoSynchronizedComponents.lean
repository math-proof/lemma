/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem sixVertexDegreeTwoSynchronizedGraph_predecessors_reachable
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Reachable
      (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d)
      (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d) := by
  by_cases heq : sixVertexDegreeTwoBranchPredecessor homega heta hdegree
      false d = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d
  · simpa [heq] using (SimpleGraph.Reachable.refl
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree)
      (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d))
  · exact SimpleGraph.Adj.reachable ⟨heq, d, Or.inl ⟨rfl, rfl⟩⟩


end
end StatMech.FrontierD
