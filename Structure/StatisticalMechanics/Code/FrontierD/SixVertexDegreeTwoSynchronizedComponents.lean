/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part3


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

structure SixVertexDegreeTwoSynchronizedHighChargeSeed
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    where
  first : SixVertexOrientedDisagreementDart omega eta
  second : SixVertexOrientedDisagreementDart omega eta
  distinct : first ≠ second
  first_mem : first ∈
    sixVertexDegreeTwoSynchronizedComponentPositiveDarts homega heta hdegree component
  second_mem : second ∈
    sixVertexDegreeTwoSynchronizedComponentPositiveDarts homega heta hdegree component
  connected :
    (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Reachable first second


end
end StatMech.FrontierD
