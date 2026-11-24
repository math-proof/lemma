module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part20


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

def SixVertexDegreeTwoSynchronizedHighChargeSeed.GloballySynchronized
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) : Prop :=
  ∀ d, seed.synchronizedAt d


end
end StatMech.FrontierD
