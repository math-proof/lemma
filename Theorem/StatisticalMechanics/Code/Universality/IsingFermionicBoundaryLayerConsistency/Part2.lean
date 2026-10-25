/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part6
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryLayerConsistency


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexGhostLayerBarrier_nonneg (n : Nat) :
    forall x, 0 <= vertexGhostLayerBarrier n x := by
  intro x
  cases x <;> simp [vertexGhostLayerBarrier,
    isingFermionicGhostCoefficient_pos.le]

theorem faceGhostLayerBarrier_nonneg (n : Nat) :
    forall c, 0 <= faceGhostLayerBarrier n c := by
  intro c
  cases c <;> simp [faceGhostLayerBarrier,
    isingFermionicGhostCoefficient_pos.le]

theorem vertexGhostLayerBarrier_le (n : Nat) :
    forall x, vertexGhostLayerBarrier n x <=
      1 / isingFermionicGhostCoefficient := by
  intro x
  cases x <;> simp [vertexGhostLayerBarrier,
    isingFermionicGhostCoefficient_pos.le]

theorem faceGhostLayerBarrier_le (n : Nat) :
    forall c, faceGhostLayerBarrier n c <=
      1 / isingFermionicGhostCoefficient := by
  intro c
  cases c <;> simp [faceGhostLayerBarrier,
    isingFermionicGhostCoefficient_pos.le]

theorem vertexGhostLayerBarrier_laplacian
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexGhostLayerBarrier n) (some x) =
      -(fkIsingSquareFullVertexGhostMultiplicity n x : Real) := by
  change isingFiniteWeightedLaplacian
    (isingFiniteGhostConductance (fkIsingSquareFullVertexGraph n)
      (isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n)))
    (vertexGhostLayerBarrier n) (some x) = _
  rw [show vertexGhostLayerBarrier n =
      isingFiniteGhostExtension 0
        (fun _ => 1 / isingFermionicGhostCoefficient) by
    funext z
    cases z <;> rfl,
    isingFiniteGhostLaplacian_some]
  simp only [isingFiniteGraphLaplacian]
  simp only [sub_self, Finset.sum_const_zero, zero_add]
  unfold isingFermionicGhostRate
  field_simp [isingFermionicGhostCoefficient_pos.ne']
  ring

theorem faceGhostLayerBarrier_laplacian
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceGhostLayerBarrier n) (some c) =
      -(fkIsingSquareFullFaceGhostMultiplicity n c : Real) := by
  change isingFiniteWeightedLaplacian
    (isingFiniteGhostConductance (fkIsingSquareFullFaceGraph n)
      (isingFermionicGhostRate
        (fkIsingSquareFullFaceGhostMultiplicity n)))
    (faceGhostLayerBarrier n) (some c) = _
  rw [show faceGhostLayerBarrier n =
      isingFiniteGhostExtension 0
        (fun _ => 1 / isingFermionicGhostCoefficient) by
    funext z
    cases z <;> rfl,
    isingFiniteGhostLaplacian_some]
  simp only [isingFiniteGraphLaplacian]
  simp only [sub_self, Finset.sum_const_zero, zero_add]
  unfold isingFermionicGhostRate
  field_simp [isingFermionicGhostCoefficient_pos.ne']
  ring

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
