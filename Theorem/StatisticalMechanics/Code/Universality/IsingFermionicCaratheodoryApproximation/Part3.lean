/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicScalingReduction
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
open Filter Set Topology Metric


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


variable (I : A.HolderInterpolation)


variable (B : A.BoundarySampling)


theorem boundary_error_le_mesh
    (n : Nat) (v : (A.P n).V) (hv : B.boundary n v) :
    |B.discreteDatum n v - (B.Phi (A.vertexEmbedding n v)).im| ≤
      B.lipschitzConstant * A.mesh n := by
  let w : {u : (A.P n).V // B.boundary n u} := ⟨v, hv⟩
  rw [show B.discreteDatum n v = (B.Phi (B.projection n w)).im by
    exact B.discreteDatum_eq_projection n w]
  rw [← Real.dist_eq]
  calc
    dist (B.Phi (B.projection n w)).im
        (B.Phi (A.vertexEmbedding n v)).im ≤
        B.lipschitzConstant *
          dist (B.projection n w) (A.vertexEmbedding n v) :=
      B.imPhi_lipschitz.dist_le_mul _ _
    _ = B.lipschitzConstant *
        dist (A.vertexEmbedding n v) (B.projection n w) := by
      rw [dist_comm]
    _ ≤ B.lipschitzConstant * A.mesh n := by
      exact mul_le_mul_of_nonneg_left
        (B.projection_dist_le_mesh n w) B.lipschitzConstant.2


theorem boundary_data_tendsto_uniformly :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ v, B.boundary n v →
        |B.discreteDatum n v - (B.Phi (A.vertexEmbedding n v)).im| < eta := by
  intro eta heta
  have htend : Tendsto (fun n ↦ (B.lipschitzConstant : Real) * A.mesh n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul A.mesh_tendsto_zero
  have hevent : ∀ᶠ n in atTop,
      (B.lipschitzConstant : Real) * A.mesh n < eta :=
    htend (Iio_mem_nhds heta)
  filter_upwards [hevent] with n hn
  intro v hv
  exact lt_of_le_of_lt (boundary_error_le_mesh A B n v hv) hn

end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
