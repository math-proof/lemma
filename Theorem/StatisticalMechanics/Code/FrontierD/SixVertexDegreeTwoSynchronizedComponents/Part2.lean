/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part2


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem sixVertexDegreeTwoSynchronizedEdgeTransition_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (edge : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Dart) :
    (edge.1.1 = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false
        (sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree edge) /\
      edge.1.2 = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true
        (sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree edge)) \/
    (edge.1.2 = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false
        (sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree edge) /\
      edge.1.1 = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true
        (sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree edge)) :=
  Classical.choose_spec edge.2.2


end
end StatMech.FrontierD
