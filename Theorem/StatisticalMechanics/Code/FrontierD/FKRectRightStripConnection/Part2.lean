/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectInducedConditionalLower.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part2


namespace StatMech.FrontierD

noncomputable section

theorem fkRectIndexedPatternEvent_dependsOnOutsideRegion
    (R : FKRectTorus) (S : Set R.Vertex)
    (I : Finset R.EdgeIndex) (eta : R.Configuration)
    (hI : ∀ a ∈ I, fkRectTorusIndexedEdge R a ∉
      Set.range (FK.ocd_innerEdge
        (Subtype.val : FKRectInducedVertex R S → R.Vertex))) :
    FKRectDependsOnOutsideRegion R S
      (fkRectIndexedPatternEvent R I eta) := by
  intro omega tau hot
  constructor
  · intro homega a ha
    exact (hot a (hI a ha)).symm.trans (homega a ha)
  · intro htau a ha
    exact (hot a (hI a ha)).trans (htau a ha)


theorem fkRectVerticalSeamPattern_dependsOnOutsideRightStripBand
    (R : FKRectTorus) (cut lower upper : Nat) (hlower : 1 ≤ lower)
    (I : Finset R.EdgeIndex)
    (hI : ∀ a ∈ I,
      fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a))
    (eta : R.Configuration) :
    FKRectDependsOnOutsideRegion R
      (fkRectRightStripBand R cut lower upper)
      (fkRectIndexedPatternEvent R I eta) := by
  apply fkRectIndexedPatternEvent_dependsOnOutsideRegion
  intro a ha
  exact fkRect_verticalSeam_not_rightStripBand_innerEdgeRange
    R cut lower upper hlower (hI a ha)


end
end StatMech.FrontierD
