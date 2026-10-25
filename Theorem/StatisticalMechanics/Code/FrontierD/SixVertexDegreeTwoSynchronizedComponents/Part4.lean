/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem sixVertexDegreeTwoSynchronizedHighChargeSeed_nonempty
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hcharge : 2 ≤
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component) :
    Nonempty
      (SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
        component) := by
  classical
  obtain ⟨first, second, hne, hfirst, hsecond⟩ :=
    exists_two_sixVertexDegreeTwoSynchronizedComponentPositiveDarts
      homega heta hdegree component hcharge
  have hfirstComponent :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
          first = component :=
    (Finset.mem_filter.mp hfirst).2.1
  have hsecondComponent :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
          second = component :=
    (Finset.mem_filter.mp hsecond).2.1
  have hconnected :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Reachable
        first second :=
    ConnectedComponent.exact
      (hfirstComponent.trans hsecondComponent.symm)
  exact ⟨⟨first, second, hne, hfirst, hsecond, hconnected⟩⟩


end
end StatMech.FrontierD
