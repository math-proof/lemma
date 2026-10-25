/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamPatternPreservation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierPattern


namespace StatMech.FrontierD

noncomputable section

theorem fkRectForceIndexedPattern_innerRestrict_eq_of_outside
    (R : FKRectTorus) (S : Set R.Vertex)
    (I : Finset R.EdgeIndex) (eta omega : R.Configuration)
    (hI : ∀ a ∈ I,
      fkRectTorusIndexedEdge R a ∉
        Set.range (FK.ocd_innerEdge
          (Subtype.val : FKRectInducedVertex R S -> R.Vertex))) :
    FK.ocd_innerRestrict
        (Subtype.val : FKRectInducedVertex R S -> R.Vertex)
        (fkRectFullGraphConfiguration R
          (fkRectForceIndexedPattern R I eta omega)) =
      FK.ocd_innerRestrict
        (Subtype.val : FKRectInducedVertex R S -> R.Vertex)
        (fkRectFullGraphConfiguration R omega) := by
  funext e
  let E := FK.ocd_innerEdge
    (Subtype.val : FKRectInducedVertex R S -> R.Vertex) e
  by_cases hE : E ∈ (fkRectTorusGraph R).edgeSet
  · let a : R.EdgeIndex :=
      (fkRectEdgeGraphEquiv R).symm ⟨E, hE⟩
    have haedge : fkRectTorusIndexedEdge R a = E := by
      exact fkRectEdgeGraphEquiv_symm_indexedEdge R ⟨E, hE⟩
    have ha : a ∉ I := by
      intro ha
      apply hI a ha
      rw [haedge]
      exact ⟨e, rfl⟩
    change fkRectFullGraphConfiguration R
        (fkRectForceIndexedPattern R I eta omega) E =
      fkRectFullGraphConfiguration R omega E
    rw [← haedge, fkRectFullGraphConfiguration_indexedEdge,
      fkRectFullGraphConfiguration_indexedEdge,
      fkRectForceIndexedPattern_of_not_mem R eta omega ha]
  · change fkRectFullGraphConfiguration R
        (fkRectForceIndexedPattern R I eta omega) E =
      fkRectFullGraphConfiguration R omega E
    rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ hE,
      fkRectFullGraphConfiguration_eq_false_of_not_edge R _ hE]


theorem fkRectForceHorizontalCut_innerRestrict_rightBand_eq
    (R : FKRectTorus) (cut lower upper : Nat) (hlower : 1 <= lower)
    (eta omega : R.Configuration) :
    FK.ocd_innerRestrict
        (Subtype.val :
          FKRectRightStripBandVertex R cut lower upper -> R.Vertex)
        (fkRectFullGraphConfiguration R
          (fkRectForceIndexedPattern R
            (fkRectHorizontalCutEdges R) eta omega)) =
      FK.ocd_innerRestrict
        (Subtype.val :
          FKRectRightStripBandVertex R cut lower upper -> R.Vertex)
        (fkRectFullGraphConfiguration R omega) := by
  apply fkRectForceIndexedPattern_innerRestrict_eq_of_outside
  intro a ha
  exact fkRect_verticalSeam_not_rightStripBand_innerEdgeRange
    R cut lower upper hlower
      (fkRectHorizontalCutEdge_crossesVerticalSeam R a ha)


theorem fkRectForceDualPullbackSeam_preserves_rightBand_chain
    (R : FKRectTorus) (cut lower upper : Nat) (hlower : 1 <= lower)
    (eta omega : R.Configuration)
    (t : Finset (FKRectRightStripBandVertex R cut lower upper ×
      FKRectRightStripBandVertex R cut lower upper))
    (hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectRightStripBandVertex R cut lower upper -> R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R cut lower upper) t) :
    FK.ocd_innerRestrict
        (Subtype.val :
          FKRectRightStripBandVertex R cut lower upper -> R.Vertex)
        (fkRectFullGraphConfiguration R
          (fkRectForceIndexedPattern R
            (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
            eta omega)) ∈
      fkRectInducedConnectionChainEvent R
        (fkRectRightStripBand R cut lower upper) t := by
  rw [fkRectDualPullbackIndexSet_horizontalCutEdges,
    fkRectForceHorizontalCut_innerRestrict_rightBand_eq
      R cut lower upper hlower]
  exact hchain


end
end StatMech.FrontierD
