/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicScalingReduction
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part2
open Filter Set Topology Metric


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


variable (I : A.HolderInterpolation)


structure BoundarySampling where
  boundary : ∀ n, (A.P n).V → Prop
  Phi : Complex → Complex
  lipschitzConstant : NNReal
  imPhi_lipschitz : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im)
  projection : ∀ n, {v : (A.P n).V // boundary n v} → Complex
  projection_mem_boundary : ∀ n v, projection n v ∈ frontier A.U
  projection_dist_le_mesh : ∀ n v,
    dist (A.vertexEmbedding n v.1) (projection n v) ≤ A.mesh n
  discreteDatum : ∀ n, (A.P n).V → Real
  discreteDatum_eq_projection : ∀ n v,
    discreteDatum n v.1 = (Phi (projection n v)).im

end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
