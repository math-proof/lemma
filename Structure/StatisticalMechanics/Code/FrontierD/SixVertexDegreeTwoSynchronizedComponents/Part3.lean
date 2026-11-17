/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part12


namespace StatMech.FrontierD

open SimpleGraph

public noncomputable section

set_option maxHeartbeats 800000

structure SixVertexDegreeTwoSynchronizedExactBoundaryTarget
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) where
  pairing : Bool -> FKMedialLoopPairing T
  boundary_eq :
    fkColoredLayeredStrandSlotBoundaryPerm pairing = seed.desiredTargetBoundary


end
end StatMech.FrontierD
