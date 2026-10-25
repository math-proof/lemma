/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part3


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.windingColumns_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.firstWindingColumn ≠ seed.secondWindingColumn := by
  intro hcolumn
  apply seed.firstSeamEdge_ne_secondSeamEdge
  apply Prod.ext
  · exact seed.firstSeamEdge_shape.1.trans seed.secondSeamEdge_shape.1.symm
  · apply Prod.ext
    · exact hcolumn
    · exact seed.firstSeamEdge_shape.2.trans seed.secondSeamEdge_shape.2.symm


end
end StatMech.FrontierD
