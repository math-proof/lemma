/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialRegularity.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part7
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiscreteInterpolation.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicProjectedFullMedialInterpolation.Part2
open Filter Metric Set Topology


noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC


namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


variable {tangent : ∀ n, A.M n → Complex}

variable (I : A.StableFullMedialInterpolation tangent)

theorem StableFullMedialInterpolation.hasCompactLocalBounds_of_holder_anchor
    (H : MeshUniformFullHolder I.interpolant)
    (B : Real) (hanchor : ∀ n, ‖I.interpolant n A.root‖ ≤ B) :
    I.HasCompactLocalBounds := by
  intro K hK _hKU
  have hdistContinuous : Continuous (fun z : Complex => dist z A.root) :=
    continuous_id.dist continuous_const
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn
    hdistContinuous.continuousOn
  refine ⟨B + (H.constant : Real) * D ^ (H.exponent : Real), ?_⟩
  intro n z hz
  calc
    ‖I.interpolant n z‖ ≤ ‖I.interpolant n A.root‖ +
        ‖I.interpolant n z - I.interpolant n A.root‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ = ‖I.interpolant n A.root‖ +
        dist (I.interpolant n z) (I.interpolant n A.root) := by
      rw [dist_eq_norm]
    _ ≤ B + (H.constant : Real) * dist z A.root ^ (H.exponent : Real) :=
      add_le_add (hanchor n) ((H.holder n).dist_le z A.root)
    _ ≤ B + (H.constant : Real) * D ^ (H.exponent : Real) := by
      gcongr
      simpa [Real.norm_of_nonneg dist_nonneg] using hD z hz

theorem StableFullMedialInterpolation.locallyUniformlySequentiallyPrecompact
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (hbounded : I.HasCompactLocalBounds) :
    StatMech.FrontierA.IsLocallyUniformlySequentiallyPrecompact
      I.interpolant A.U :=
  StatMech.FrontierA.equicontinuousFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
    I.interpolant A.U A.isOpen I.compactEquicontinuous hbounded E

end FKIsingCaratheodoryApproximation
end StatMech.Universality
end
