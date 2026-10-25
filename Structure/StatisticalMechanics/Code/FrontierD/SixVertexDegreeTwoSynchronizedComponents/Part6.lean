/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part16


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

structure SixVertexDegreeTwoSynchronizedSupportedExactBoundaryTarget
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) where
  target : SixVertexDegreeTwoSynchronizedExactBoundaryTarget seed
  seamDelta_false : target.colorSplice.seamDelta false = 1
  seamDelta_true : target.colorSplice.seamDelta true = -1
  fine :
    sixVertexHorizontalPairBoundedFineRowProfile
        (((target.colorSplice.target false).arrows.horizontal,
          (target.colorSplice.target true).arrows.horizontal)) =
      sixVertexHorizontalPairBoundedFineRowProfile
        (((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
          false).arrows.horizontal,
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
            true).arrows.horizontal))
  twoCycle :
    sixVertexPairAtMostTwoCycleRelated
      ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
          false).arrows,
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
          true).arrows)
      ((target.colorSplice.target false).arrows,
        (target.colorSplice.target true).arrows)


end
end StatMech.FrontierD
