/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part2


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

noncomputable def sixVertexDegreeTwoSynchronizedComponentCharge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :
    Int := by
  classical
  exact ∑ d : SixVertexOrientedDisagreementDart omega eta,
    if (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk d =
        component then sixVertexDegreeTwoStrandStepSeamSign hdegree d else 0

noncomputable def sixVertexDegreeTwoSynchronizedTotalComponentCharge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) : Int :=
  ∑ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
    sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component


noncomputable def sixVertexDegreeTwoSynchronizedComponentPositiveDarts
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :
    Finset (SixVertexOrientedDisagreementDart omega eta) := by
  classical
  exact Finset.univ.filter fun dart =>
    (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
        dart = component /\
      sixVertexDegreeTwoStrandStepSeamSign hdegree dart = 1


end
end StatMech.FrontierD
