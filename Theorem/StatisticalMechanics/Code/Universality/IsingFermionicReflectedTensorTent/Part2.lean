/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectedTensorTent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflection.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
open Filter Metric Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)

variable (G : BoundaryRadialTensorTentGeometry A)


theorem BoundaryRadialTensorTentGeometry.reflected_tendsto_iff
    {f : Complex → Complex} :
    TendstoLocallyUniformlyOn (G.reflectedInterpolant A)
        (fun z ↦ f ((starRingEnd Complex) z)) atTop
        (reflectComplexSet A.U) ↔
      TendstoLocallyUniformlyOn
        (BoundaryRadialTensorTentGeometry.interpolant A G)
        f atTop A.U := by
  exact tendstoLocallyUniformlyOn_reflect_iff

end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
