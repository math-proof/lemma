/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part26
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexGhostConductance_nonneg (n : Nat) :
    ∀ x y, 0 ≤ vertexGhostConductance n x y := by
  exact isingFiniteGhostConductance_nonneg
    (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n))
    (isingFermionicGhostRate_nonneg
      (fkIsingSquareFullVertexGhostMultiplicity n))

theorem vertexGhostConductance_pos_of_adj (n : Nat) :
    ∀ ⦃x y⦄, (vertexGhostGraph n).Adj x y →
      0 < vertexGhostConductance n x y := by
  exact isingFiniteGhostConductance_pos_of_adj
    (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n))

theorem vertexGhost_reaches_boundary (n : Nat) :
    ∀ x, ∃ b, vertexDirichletBoundary n b ∧
      (vertexGhostGraph n).Reachable x b := by
  apply isingFiniteGhostGraph_reachable_boundaryWith
    (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n))
    (fkIsingSquareFullVertexFixedBoundary n)
  intro x
  obtain ⟨b, hb, hxb⟩ := fkIsingSquareFullVertex_reaches_fixed_or_ghost n x
  refine ⟨b, ?_, hxb⟩
  rcases hb with hb | hb
  · exact Or.inl hb
  · exact Or.inr ((isingFermionicGhostRate_pos_iff
      (fkIsingSquareFullVertexGhostMultiplicity n) b).2 hb)

theorem faceGhostConductance_nonneg (n : Nat) :
    ∀ x y, 0 ≤ faceGhostConductance n x y := by
  exact isingFiniteGhostConductance_nonneg
    (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n))
    (isingFermionicGhostRate_nonneg
      (fkIsingSquareFullFaceGhostMultiplicity n))

theorem faceGhostConductance_pos_of_adj (n : Nat) :
    ∀ ⦃x y⦄, (faceGhostGraph n).Adj x y →
      0 < faceGhostConductance n x y := by
  exact isingFiniteGhostConductance_pos_of_adj
    (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n))

theorem faceGhost_reaches_boundary (n : Nat) :
    ∀ x, ∃ b, faceDirichletBoundary n b ∧
      (faceGhostGraph n).Reachable x b := by
  apply isingFiniteGhostGraph_reachable_boundaryWith
    (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n))
    (fkIsingSquareFullFaceFixedBoundary n)
  intro c
  obtain ⟨b, hb, hcb⟩ := fkIsingSquareFullFace_reaches_fixed_or_ghost n c
  refine ⟨b, ?_, hcb⟩
  rcases hb with hb | hb
  · exact Or.inl hb
  · exact Or.inr ((isingFermionicGhostRate_pos_iff
      (fkIsingSquareFullFaceGhostMultiplicity n) b).2 hb)

theorem vertexGhostPrimitive_superharmonicOn
    (n : Nat) (hn : 0 < n) :
    IsingFiniteWeightedSuperharmonicOn (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn) := by
  exact isingFiniteGhostExtension_superharmonicOn_boundaryWith
    (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n))
    (fkIsingSquareFullVertexFixedBoundary n) 1
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
    (vertex_modifiedLaplacian_nonpos_of_not_wiredArc n hn)

theorem faceGhostPrimitive_subharmonicOn
    (n : Nat) (hn : 0 < n) :
    IsingFiniteWeightedSubharmonicOn (faceGhostConductance n)
      (faceDirichletBoundary n) (faceGhostPrimitive n hn) := by
  exact isingFiniteGhostExtension_subharmonicOn_boundaryWith
    (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n))
    (fkIsingSquareFullFaceFixedBoundary n) 0
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
    (face_modifiedLaplacian_nonneg_of_not_fixedBoundary n hn)


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
