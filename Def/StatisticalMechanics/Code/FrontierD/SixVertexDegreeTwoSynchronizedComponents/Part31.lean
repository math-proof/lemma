module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part33


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

noncomputable def sixVertexDegreeTwoSynchronizedReconnectionSeed
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    SixVertexDegreeTwoSynchronizedReconnectionSeed homega heta hdegree :=
  Classical.choice
    (sixVertexDegreeTwoSynchronizedReconnectionSeed_nonempty homega heta
      hdegree middle homegaSector hetaSector hmiddle)

end
end StatMech.FrontierD
