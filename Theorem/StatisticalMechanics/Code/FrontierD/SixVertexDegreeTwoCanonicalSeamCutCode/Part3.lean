/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalSeamCutCode.Part3


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.canonicalWindingColumns_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    seed.firstWindingColumn ≠ seed.nextPositiveWindingColumn hsame := by
  intro hcolumn
  apply seed.firstSeamEdge_ne_nextPositiveSeamEdge hsame
  apply Prod.ext
  · exact seed.firstSeamEdge_shape.1.trans
      (seed.nextPositiveSeamEdge_shape hsame).1.symm
  · apply Prod.ext
    · exact hcolumn
    · exact seed.firstSeamEdge_shape.2.trans
        (seed.nextPositiveSeamEdge_shape hsame).2.symm


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.sameStrandArcPair_first_physical
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    ((seed.sameStrandArcPair hsame).first.edge
      (seed.sameStrandArcPair hsame).first.firstIndex).physical =
        sixVertexTorusEdgePhysical seed.firstSeamEdge := by
  change (sixVertexDegreeTwoOrientedStrandEdge hdegree
    (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed.first
      (sixVertexFinPrefixIndex (seed.nextPositiveIndex hsame)
        ⟨0, seed.nextPositiveIndex_val_pos hsame⟩))).physical = _
  unfold sixVertexDegreeTwoOrientedStrandEdge
  rw [sixVertexDirectedTorusEdgeOfArrow_physical]
  apply congrArg sixVertexTorusEdgePhysical
  change sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed.first
          (sixVertexFinPrefixIndex (seed.nextPositiveIndex hsame)
            ⟨0, seed.nextPositiveIndex_val_pos hsame⟩))).1 =
    sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree seed.first.1).1
  rw [show sixVertexFinPrefixIndex (seed.nextPositiveIndex hsame)
      ⟨0, seed.nextPositiveIndex_val_pos hsame⟩ =
        sixVertexDegreeTwoStrandCycleZeroIndex
          homega heta hdegree seed.first by
      apply Fin.ext
      rfl,
    sixVertexDegreeTwoStrandCycleEnumeration_zero]


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.sameStrandArcPair_second_physical
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    ((seed.sameStrandArcPair hsame).second.edge
      (seed.sameStrandArcPair hsame).second.firstIndex).physical =
        sixVertexTorusEdgePhysical (seed.nextPositiveSeamEdge hsame) := by
  change (sixVertexDegreeTwoOrientedStrandEdge hdegree
    (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed.first
      (sixVertexFinSuffixIndex (seed.nextPositiveIndex hsame)
        ⟨0, by omega⟩))).physical = _
  unfold sixVertexDegreeTwoOrientedStrandEdge
  rw [sixVertexDirectedTorusEdgeOfArrow_physical]
  apply congrArg sixVertexTorusEdgePhysical
  change sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed.first
          (sixVertexFinSuffixIndex (seed.nextPositiveIndex hsame)
            ⟨0, by omega⟩))).1 =
    sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree (seed.nextPositiveDart hsame).1).1
  rw [show sixVertexFinSuffixIndex (seed.nextPositiveIndex hsame)
      ⟨0, by omega⟩ = seed.nextPositiveIndex hsame by
      apply Fin.ext
      simp]
  rfl


end
end StatMech.FrontierD
