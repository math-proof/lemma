/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part15


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

namespace SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets

@[simp] theorem key_splice
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (paired : SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets seed)
    (choice : Bool) :
    (paired.key choice).splice =
      (paired.branch choice).target.toSplice := by
  rfl


@[simp] theorem key_recovers_source
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (paired : SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets seed)
    (choice : Bool) :
    (paired.key choice).splice.symm.target =
      sixVertexDegreeTwoAlignedColoredSource homega heta hdegree :=
  (paired.key choice).toFKColoredUnitTransferRoutedKey.recover


theorem key_target_distinct
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (paired : SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets seed) :
    (paired.key false).splice.target ≠
      (paired.key true).splice.target := by
  simpa using paired.target_distinct

end SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets
end
end StatMech.FrontierD
