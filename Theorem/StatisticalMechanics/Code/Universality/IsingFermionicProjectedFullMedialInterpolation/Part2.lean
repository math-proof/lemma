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
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicProjectedFullMedialInterpolation
open Filter Metric Set Topology


noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC


namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


theorem MeshUniformFullHolder.equicontinuous
    {F : Nat → Complex → Complex} (H : MeshUniformFullHolder F) :
    Equicontinuous F := by
  apply UniformEquicontinuous.equicontinuous
  apply Metric.uniformEquicontinuous_of_continuity_modulus
    (fun d : Real => (H.constant : Real) * d ^ (H.exponent : Real))
  · have hp : (0 : Real) < (H.exponent : Real) := H.exponent_pos
    have ht := (Real.continuousAt_rpow_const 0 (H.exponent : Real)
      (Or.inr hp.le)).tendsto.const_mul (H.constant : Real)
    simpa [Real.zero_rpow hp.ne'] using ht
  · intro x y n
    exact (H.holder n).dist_le x y


end FKIsingCaratheodoryApproximation
end StatMech.Universality
end
