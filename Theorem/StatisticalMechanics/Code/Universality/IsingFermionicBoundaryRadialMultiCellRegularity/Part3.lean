/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Mathlib.Algebra.Order.Chebyshev
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


theorem MeshUniformCompactHolder.equicontinuousOn
    {F : Nat → Complex → Complex} (H : A.MeshUniformCompactHolder F)
    (K : Set Complex) (hK : IsCompact K) (hKU : K ⊆ A.U) :
    EquicontinuousOn F K := by
  obtain ⟨C, alpha, halpha, hholder⟩ := H.holder K hK hKU
  rw [← equicontinuous_restrict_iff]
  apply UniformEquicontinuous.equicontinuous
  apply Metric.uniformEquicontinuous_of_continuity_modulus
    (fun d : Real ↦ (C : Real) * d ^ (alpha : Real))
  · have hp : (0 : Real) < (alpha : Real) := halpha
    have ht := (Real.continuousAt_rpow_const 0 (alpha : Real)
      (Or.inr hp.le)).tendsto.const_mul (C : Real)
    simpa [Real.zero_rpow hp.ne'] using ht
  · intro x y n
    simpa using (hholder n).dist_le x.property y.property


end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
