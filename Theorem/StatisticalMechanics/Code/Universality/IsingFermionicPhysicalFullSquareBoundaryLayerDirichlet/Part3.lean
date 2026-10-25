/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part26
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem faceDirichlet_harmonicOn
    (n : Nat) (hn : 0 < n) :
    IsingFiniteWeightedHarmonicOn (faceGhostConductance n)
      (faceDirichletBoundary n) (faceDirichlet n hn) :=
  (Classical.choose_spec (isingFiniteWeighted_exists_harmonic_extension
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceGhostPrimitive n hn))).1

theorem faceDirichlet_boundary
    (n : Nat) (hn : 0 < n) (c : Option (FKIsingSquareFullFaceNode n))
    (hc : faceDirichletBoundary n c) :
    faceDirichlet n hn c = faceGhostPrimitive n hn c :=
  (Classical.choose_spec (isingFiniteWeighted_exists_harmonic_extension
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceGhostPrimitive n hn))).2 c hc

theorem vertexDirichlet_le_ghostPrimitive
    (n : Nat) (hn : 0 < n) :
    ∀ x, vertexDirichlet n hn x ≤ vertexGhostPrimitive n hn x := by
  apply isingFiniteWeighted_harmonic_le_superharmonic
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexDirichlet n hn)
    (vertexGhostPrimitive n hn) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexDirichlet_harmonicOn n hn)
    (vertexGhostPrimitive_superharmonicOn n hn)
  intro x hx
  exact (vertexDirichlet_boundary n hn x hx).le

theorem faceGhostPrimitive_le_dirichlet
    (n : Nat) (hn : 0 < n) :
    ∀ c, faceGhostPrimitive n hn c ≤ faceDirichlet n hn c := by
  apply isingFiniteWeighted_subharmonic_le_harmonic
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostPrimitive n hn)
    (faceDirichlet n hn) (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceGhostPrimitive_subharmonicOn n hn)
    (faceDirichlet_harmonicOn n hn)
  intro c hc
  exact (faceDirichlet_boundary n hn c hc).ge

theorem vertexDirichlet_nonneg
    (n : Nat) (hn : 0 < n) : ∀ x, 0 ≤ vertexDirichlet n hn x := by
  apply isingFiniteWeighted_const_le_superharmonic
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexDirichlet n hn) 0
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)
  · intro x hx
    exact (vertexDirichlet_harmonicOn n hn x hx).le
  · intro x hx
    rw [vertexDirichlet_boundary n hn x hx]
    cases x with
    | none => simp [vertexGhostPrimitive, isingFiniteGhostExtension]
    | some x =>
        change fkIsingSquareFullVertexFixedBoundary n x at hx
        simp [vertexGhostPrimitive, isingFiniteGhostExtension,
          vertex_fixedBoundary_eq_zero n hn x hx]

theorem vertexDirichlet_le_one
    (n : Nat) (hn : 0 < n) : ∀ x, vertexDirichlet n hn x ≤ 1 := by
  apply isingFiniteWeighted_subharmonic_le_const
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexDirichlet n hn) 1
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)
  · intro x hx
    exact (vertexDirichlet_harmonicOn n hn x hx).ge
  · intro x hx
    rw [vertexDirichlet_boundary n hn x hx]
    cases x with
    | none => simp [vertexGhostPrimitive, isingFiniteGhostExtension]
    | some x =>
        change fkIsingSquareFullVertexFixedBoundary n x at hx
        simp [vertexGhostPrimitive, isingFiniteGhostExtension,
          vertex_fixedBoundary_eq_zero n hn x hx]

theorem faceDirichlet_nonneg
    (n : Nat) (hn : 0 < n) : ∀ c, 0 ≤ faceDirichlet n hn c := by
  apply isingFiniteWeighted_const_le_superharmonic
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceDirichlet n hn) 0
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)
  · intro c hc
    exact (faceDirichlet_harmonicOn n hn c hc).le
  · intro c hc
    rw [faceDirichlet_boundary n hn c hc]
    cases c with
    | none => simp [faceGhostPrimitive, isingFiniteGhostExtension]
    | some c =>
        change fkIsingSquareFullFaceFixedBoundary n c at hc
        simp [faceGhostPrimitive, isingFiniteGhostExtension,
          face_fixedBoundary_eq_one n hn c hc]

theorem faceDirichlet_le_one
    (n : Nat) (hn : 0 < n) : ∀ c, faceDirichlet n hn c ≤ 1 := by
  apply isingFiniteWeighted_subharmonic_le_const
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceDirichlet n hn) 1
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)
  · intro c hc
    exact (faceDirichlet_harmonicOn n hn c hc).ge
  · intro c hc
    rw [faceDirichlet_boundary n hn c hc]
    cases c with
    | none => simp [faceGhostPrimitive, isingFiniteGhostExtension]
    | some c =>
        change fkIsingSquareFullFaceFixedBoundary n c at hc
        simp [faceGhostPrimitive, isingFiniteGhostExtension,
          face_fixedBoundary_eq_one n hn c hc]


theorem physicalIncidence_dirichlet_sandwich
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    vertexDirichlet n hn
          (some (fkIsingSquareInteriorRadialEndpoint n hn e)) ≤
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareInteriorRadialEndpoint n hn e) ∧
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareInteriorRadialEndpoint n hn e) ≤
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn e) ∧
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn e) ≤
        faceDirichlet n hn
          (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) := by
  constructor
  · simpa [vertexGhostPrimitive] using
      vertexDirichlet_le_ghostPrimitive n hn
        (some (fkIsingSquareInteriorRadialEndpoint n hn e))
  constructor
  · exact fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face n hn e
  · simpa [faceGhostPrimitive] using
      faceGhostPrimitive_le_dirichlet n hn
        (some (fkIsingSquareFullFaceOfRadialIncidence n hn e))


theorem physicalIncidence_close_of_dirichlet_close
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn)
    (target eps : Real)
    (hvertex : |vertexDirichlet n hn
        (some (fkIsingSquareInteriorRadialEndpoint n hn e)) - target| ≤ eps)
    (hface : |faceDirichlet n hn
        (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) - target| ≤ eps) :
    |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareInteriorRadialEndpoint n hn e) - target| ≤ eps ∧
      |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (fkIsingSquareFullFaceOfRadialIncidence n hn e) - target| ≤ eps := by
  rcases physicalIncidence_dirichlet_sandwich n hn e with
    ⟨hDirVertex, hVertexFace, hFaceDir⟩
  rw [abs_le] at hvertex hface
  constructor
  · rw [abs_le]
    constructor <;> linarith [hvertex.1, hface.2]
  · rw [abs_le]
    constructor <;> linarith [hvertex.1, hface.2]


theorem radialPatch_unitRange_and_dirichlet_sandwich
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) :
    ((∀ p, 0 ≤ radialPatchPrimalValue n m hn hm p ∧
        radialPatchPrimalValue n m hn hm p ≤ 1) ∧
      (∀ q, 0 ≤ radialPatchDualValue n m hn hm hm2 q ∧
        radialPatchDualValue n m hn hm hm2 q ≤ 1)) ∧
      ∀ e : FKIsingSquareInteriorRadialIncidence n hn,
        vertexDirichlet n hn
              (some (fkIsingSquareInteriorRadialEndpoint n hn e)) ≤
            (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
              (fkIsingSquareInteriorRadialEndpoint n hn e) ∧
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
              (fkIsingSquareInteriorRadialEndpoint n hn e) ≤
            (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
              (fkIsingSquareFullFaceOfRadialIncidence n hn e) ∧
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
              (fkIsingSquareFullFaceOfRadialIncidence n hn e) ≤
            faceDirichlet n hn
              (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) := by
  exact ⟨radialPatch_unitRange_of_fullSquareGhost n m hn hm hm2,
    physicalIncidence_dirichlet_sandwich n hn⟩


theorem finiteSquare_integratedPrimitive_dirichletComparison
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) :
    ((∀ p, 0 ≤ radialPatchPrimalValue n m hn hm p ∧
        radialPatchPrimalValue n m hn hm p ≤ 1) ∧
      (∀ q, 0 ≤ radialPatchDualValue n m hn hm hm2 q ∧
        radialPatchDualValue n m hn hm hm2 q ≤ 1)) ∧
      (∀ x, 0 ≤ vertexDirichlet n hn x ∧ vertexDirichlet n hn x ≤ 1) ∧
      (∀ c, 0 ≤ faceDirichlet n hn c ∧ faceDirichlet n hn c ≤ 1) ∧
      ∀ e : FKIsingSquareInteriorRadialIncidence n hn,
        vertexDirichlet n hn
              (some (fkIsingSquareInteriorRadialEndpoint n hn e)) ≤
            (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
              (fkIsingSquareInteriorRadialEndpoint n hn e) ∧
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
              (fkIsingSquareInteriorRadialEndpoint n hn e) ≤
            (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
              (fkIsingSquareFullFaceOfRadialIncidence n hn e) ∧
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
              (fkIsingSquareFullFaceOfRadialIncidence n hn e) ≤
            faceDirichlet n hn
              (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) := by
  refine ⟨radialPatch_unitRange_of_fullSquareGhost n m hn hm hm2,
    ?_, ?_, physicalIncidence_dirichlet_sandwich n hn⟩
  · intro x
    exact ⟨vertexDirichlet_nonneg n hn x, vertexDirichlet_le_one n hn x⟩
  · intro c
    exact ⟨faceDirichlet_nonneg n hn c, faceDirichlet_le_one n hn c⟩

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
