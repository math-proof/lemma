/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency.Part2


namespace StatMech.Universality

open Finset SimpleGraph Filter Metric Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertex_fixed_ghost_mem_markedEndpointLayer
    (n radius : Nat) (x : FKIsingSquareFullVertexNode n)
    (hfixed : fkIsingSquareFullVertexFixedBoundary n x)
    (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity n x) :
    vertexMarkedEndpointLayer n radius (some x) := by
  have hx := fkIsingSquareVertex_coordinate_bounds n x 0
  have hy := fkIsingSquareVertex_coordinate_bounds n x 1
  rw [fkIsingSquareFullVertexGhostMultiplicity_pos_iff] at hghost
  unfold fkIsingSquareFullVertexFixedBoundary fkIsingSquareWiredArc at hfixed
  unfold vertexMarkedEndpointLayer
  rcases hghost with hsouth | heast | hnorth
  · left
    simp [hfixed, hsouth]
  · have hn : n = 0 := by omega
    subst n
    have hy0 : x.1 1 = 0 := by omega
    left
    simp [hfixed, hy0]
  · right
    simp [hfixed, hnorth]


theorem vertex_adj_fixed_ghost_mem_markedEndpointLayer
    (n radius : Nat) (hradius : 0 < radius)
    (x y : FKIsingSquareFullVertexNode n)
    (hxy : (fkIsingSquareFullVertexGraph n).Adj x y)
    (hfixed : fkIsingSquareFullVertexFixedBoundary n y)
    (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity n y) :
    vertexMarkedEndpointLayer n radius (some x) := by
  have hl1 : l1dist 2 x.1 y.1 = 1 := by
    apply l1dist_of_adj
    exact hxy
  rw [fkIsingSquareFullVertexGhostMultiplicity_pos_iff] at hghost
  unfold fkIsingSquareFullVertexFixedBoundary fkIsingSquareWiredArc at hfixed
  unfold vertexMarkedEndpointLayer
  rcases hghost with hsouth | heast | hnorth
  · left
    have hdist : Int.natAbs (x.1 0 + (n : Int)) +
        Int.natAbs (x.1 1 + (n : Int)) = 1 := by
      simpa [l1dist, hfixed, hsouth] using hl1
    omega
  · have hn : n = 0 := by
      have hy := fkIsingSquareVertex_coordinate_bounds n y 0
      omega
    subst n
    have hy0 : y.1 1 = 0 := by
      have hy := fkIsingSquareVertex_coordinate_bounds 0 y 1
      omega
    left
    have hdist : Int.natAbs (x.1 0) + Int.natAbs (x.1 1) = 1 := by
      simpa [l1dist, hfixed, hy0] using hl1
    omega
  · right
    have hdist : Int.natAbs (x.1 0 + (n : Int)) +
        Int.natAbs (x.1 1 - (n : Int)) = 1 := by
      simpa [l1dist, hfixed, hnorth] using hl1
    omega


theorem face_fixed_ghost_mem_markedEndpointLayer
    (n radius : Nat) (hradius : 0 < radius)
    (c : FKIsingSquareFullFaceNode n)
    (hfixed : fkIsingSquareFullFaceFixedBoundary n c)
    (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity n c) :
    faceMarkedEndpointLayer n radius (some c) := by
  rw [fkIsingSquareFullFaceGhostMultiplicity_pos_iff] at hghost
  unfold fkIsingSquareFullFaceFixedBoundary at hfixed
  unfold faceMarkedEndpointLayer fkIsingSquareInteriorCellKey
  rcases hfixed with hsouth | heast | hnorth
  · left
    simp [hghost, hsouth]
  · omega
  · right
    simp [hghost]
    have hc : c.2.1 < 2 * n := c.2.2
    omega


theorem face_adj_fixed_ghost_mem_markedEndpointLayer
    (n radius : Nat) (hradius : 2 <= radius)
    (c d : FKIsingSquareFullFaceNode n)
    (hcd : (fkIsingSquareFullFaceGraph n).Adj c d)
    (hfixed : fkIsingSquareFullFaceFixedBoundary n d)
    (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity n d) :
    faceMarkedEndpointLayer n radius (some c) := by
  rw [fkIsingSquareFullFaceGhostMultiplicity_pos_iff] at hghost
  unfold fkIsingSquareFullFaceFixedBoundary at hfixed
  unfold faceMarkedEndpointLayer fkIsingSquareInteriorCellKey
  rcases hcd with hvertical | hhorizontal
  · have hx : c.1.1 = d.1.1 := congrArg Fin.val hvertical.1
    rcases hfixed with hsouth | heast | hnorth
    · left
      simp [hx, hghost]
      omega
    · omega
    · right
      simp [hx, hghost]
      have hc := c.2.2
      have hd := d.2.2
      rcases hvertical.2 with h | h <;> omega
  · have hy : c.2.1 = d.2.1 := congrArg Fin.val hhorizontal.1
    rcases hfixed with hsouth | heast | hnorth
    · left
      simp [hy, hsouth]
      rcases hhorizontal.2 with h | h <;> omega
    · omega
    · right
      simp [hy]
      have hc := c.1.2
      have hd := d.1.2
      rcases hhorizontal.2 with h | h <;> omega


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
