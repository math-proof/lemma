/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.windingFlows_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (row : Fin T.height) :
    seed.firstWindingFamily.verticalFlow (seed.firstWindingColumn, row) ≠
      seed.secondWindingFamily.verticalFlow (seed.firstWindingColumn, row) := by
  simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.firstWindingFamily,
    SixVertexDegreeTwoSynchronizedHighChargeSeed.secondWindingFamily,
    seed.windingColumns_ne]


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.windingTargets_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    {source : SixVertexArrows T × SixVertexArrows T}
    (first : SixVertexSignedWindingCycleTarget source
      seed.firstWindingFamily true)
    (second : SixVertexSignedWindingCycleTarget source
      seed.secondWindingFamily true) :
    first.target ≠ second.target :=
  first.targets_ne_of_signedVerticalFlow_ne second
    (seed.firstWindingColumn, svFinLast T.height_pos)
    (by simpa using seed.windingFlows_ne (svFinLast T.height_pos))

end
end StatMech.FrontierD
