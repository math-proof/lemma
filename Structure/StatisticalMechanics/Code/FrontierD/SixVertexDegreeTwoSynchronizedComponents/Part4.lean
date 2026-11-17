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
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part13


namespace StatMech.FrontierD

open SimpleGraph

public noncomputable section

set_option maxHeartbeats 800000

structure SixVertexDegreeTwoSynchronizedSupportedSplitTarget
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) where
  target : SixVertexDegreeTwoSynchronizedSplitColorTarget seed
  seamDelta_false : target.toSplice.seamDelta false = 1
  seamDelta_true : target.toSplice.seamDelta true = -1
  fine :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((target.toSplice.target false).arrows.horizontal,
          (target.toSplice.target true).arrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
          false).arrows.horizontal,
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
            true).arrows.horizontal)
  twoCycle :
    sixVertexPairAtMostTwoCycleRelated
      ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
          false).arrows,
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
          true).arrows)
      ((target.toSplice.target false).arrows,
        (target.toSplice.target true).arrows)


end
end StatMech.FrontierD
