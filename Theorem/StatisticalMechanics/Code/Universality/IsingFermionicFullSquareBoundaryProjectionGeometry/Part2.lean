/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem fullSquareVertexBoundaryProjection_mem_leftSide
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexFixedBoundary n x) :
    fullSquareVertexBoundaryProjection n scale x ∈
      fullSquareScaledLeftSide n scale := by
  change x.1 0 = -(n : Int) at hx
  simp [fullSquareScaledLeftSide, fullSquareVertexBoundaryProjection,
    fullSquareScaledVertexEmbedding, fullSquareScaledCoordinateEmbedding,
    fkIsingSquareFullVertexCoordinate, fkIsingSquareWiredIntPoint]
  rw [hx]
  push_cast
  ring

theorem fullSquareFaceFixedBoundaryProjection_mem_freeSides
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceFixedBoundary n c) :
    fullSquareFaceFixedBoundaryProjection n scale c ∈
      fullSquareScaledFreeSides n scale := by
  unfold fullSquareFaceFixedBoundaryProjection
  split_ifs with hb hr
  · refine Or.inl (Or.inl ?_)
    simp [fullSquareScaledBottomSide,
      fullSquareScaledFaceEmbedding, fullSquareScaledCoordinateEmbedding,
      fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
      fkIsingSquareWiredIntPoint]
    push_cast at hb ⊢
    rw [hb]
    ring
  · refine Or.inl (Or.inr ?_)
    simp [fullSquareScaledRightSide,
      fullSquareScaledFaceEmbedding, fullSquareScaledCoordinateEmbedding,
      fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
      fkIsingSquareWiredIntPoint]
    have hr' : (c.1.val : Real) + 1 = 2 * (n : Real) := by
      exact_mod_cast hr
    rw [show (c.1.val : Real) = 2 * (n : Real) - 1 by linarith]
    ring
  · refine Or.inr ?_
    rcases hc with hc | hc | hc
    · exact (hb hc).elim
    · exact (hr hc).elim
    · simp [fullSquareScaledTopSide,
        fullSquareScaledFaceEmbedding, fullSquareScaledCoordinateEmbedding,
        fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
        fkIsingSquareWiredIntPoint]
      have hc' : (c.2.val : Real) + 1 = 2 * (n : Real) := by
        exact_mod_cast hc
      rw [show (c.2.val : Real) = 2 * (n : Real) - 1 by linarith]
      ring

theorem fullSquareVertexFreeBoundaryProjection_mem_freeSides
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n)
    (hx : 0 < fkIsingSquareFullVertexGhostMultiplicity n x) :
    fullSquareVertexFreeBoundaryProjection n scale x ∈
      fullSquareScaledFreeSides n scale := by
  rw [fkIsingSquareFullVertexGhostMultiplicity_pos_iff] at hx
  rcases hx with hx | hx | hx
  · refine Or.inl (Or.inl ?_)
    simp [fullSquareScaledBottomSide,
      fullSquareVertexFreeBoundaryProjection,
      fullSquareScaledVertexEmbedding, fullSquareScaledCoordinateEmbedding,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareWiredIntPoint]
    rw [hx]
    push_cast
    ring
  · refine Or.inl (Or.inr ?_)
    simp [fullSquareScaledRightSide,
      fullSquareVertexFreeBoundaryProjection,
      fullSquareScaledVertexEmbedding, fullSquareScaledCoordinateEmbedding,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareWiredIntPoint]
    rw [hx]
    push_cast
    ring
  · refine Or.inr ?_
    simp [fullSquareScaledTopSide,
      fullSquareVertexFreeBoundaryProjection,
      fullSquareScaledVertexEmbedding, fullSquareScaledCoordinateEmbedding,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareWiredIntPoint]
    rw [hx]
    push_cast
    ring

theorem fullSquareFaceFreeBoundaryProjection_mem_leftSide
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n)
    (hc : 0 < fkIsingSquareFullFaceGhostMultiplicity n c) :
    fullSquareFaceFreeBoundaryProjection n scale c ∈
      fullSquareScaledLeftSide n scale := by
  rw [fkIsingSquareFullFaceGhostMultiplicity_pos_iff] at hc
  simp [fullSquareScaledLeftSide, fullSquareFaceFreeBoundaryProjection,
    fullSquareScaledFaceEmbedding, fullSquareScaledCoordinateEmbedding,
    fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
    fkIsingSquareWiredIntPoint]
  rw [hc]
  ring

@[simp] theorem fullSquareVertexBoundaryProjection_dist
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n) :
    dist (fullSquareScaledVertexEmbedding n scale x)
      (fullSquareVertexBoundaryProjection n scale x) = 0 := by
  simp [fullSquareVertexBoundaryProjection]

theorem fullSquareFaceFixedBoundaryProjection_dist_le
    (n : Nat) (scale : Real) (hscale : 0 <= scale)
    (c : FKIsingSquareFullFaceNode n) :
    dist (fullSquareScaledFaceEmbedding n scale c)
      (fullSquareFaceFixedBoundaryProjection n scale c) <= scale := by
  unfold fullSquareFaceFixedBoundaryProjection
  split_ifs
  · exact halfDiagonal_displacement_le_scale _ _
      norm_neg_one_add_I_le_two scale hscale
  · exact halfDiagonal_displacement_le_scale _ _
      norm_one_add_I_le_two scale hscale
  · exact halfDiagonal_displacement_le_scale _ _
      norm_one_sub_I_le_two scale hscale

@[simp] theorem fullSquareVertexFreeBoundaryProjection_dist
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n) :
    dist (fullSquareScaledVertexEmbedding n scale x)
      (fullSquareVertexFreeBoundaryProjection n scale x) = 0 := by
  simp [fullSquareVertexFreeBoundaryProjection]

theorem fullSquareFaceFreeBoundaryProjection_dist_le
    (n : Nat) (scale : Real) (hscale : 0 <= scale)
    (c : FKIsingSquareFullFaceNode n) :
    dist (fullSquareScaledFaceEmbedding n scale c)
      (fullSquareFaceFreeBoundaryProjection n scale c) <= scale := by
  exact halfDiagonal_displacement_le_scale _ _
    norm_neg_one_sub_I_le_two scale hscale


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
