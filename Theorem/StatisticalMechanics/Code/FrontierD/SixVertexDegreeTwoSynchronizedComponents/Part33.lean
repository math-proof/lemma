/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Inductive.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem sixVertexDegreeTwoSynchronizedReconnectionSeed_nonempty
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    Nonempty
      (SixVertexDegreeTwoSynchronizedReconnectionSeed homega heta hdegree) := by
  classical
  rcases sixVertexDegreeTwoSynchronizedComponent_unit_or_fractional
      homega heta hdegree with hunit | hnoUnit
  · obtain ⟨component, hcharge⟩ := hunit
    exact ⟨.unit component hcharge⟩
  · obtain ⟨component, hcharge⟩ :=
      exists_sixVertexDegreeTwoSynchronizedComponentCharge_ge_two_of_no_unit
        homega heta hdegree middle homegaSector hetaSector hmiddle hnoUnit
    exact ⟨.split component
      hcharge (sixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
        component hcharge)⟩


end
end StatMech.FrontierD
