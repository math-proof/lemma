/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part32


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

inductive SixVertexDegreeTwoSynchronizedReconnectionSeed
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) : Type
  | unit
      (component :
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
      (charge : sixVertexDegreeTwoSynchronizedComponentCharge homega heta
        hdegree component = 1)
  | split
      (component :
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
      (charge : 2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge homega heta
        hdegree component)
      (endpoints : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta
        hdegree component)


end
end StatMech.FrontierD
