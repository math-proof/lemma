/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryCompanionUnique.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleCompanion


namespace StatMech.FrontierD

noncomputable section

def FKRectPrimalBoundaryCompanionUnique
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  forall (x : R.Vertex)
    (C D E : FKRectConfigurationBlackBoundaryCycle R omega),
    C ∈ fkRectPrimalClusterNonzeroBoundaryCycles R omega x ->
    D ∈ fkRectPrimalClusterNonzeroBoundaryCycles R omega x ->
    E ∈ fkRectPrimalClusterNonzeroBoundaryCycles R omega x ->
    D ≠ C -> E ≠ C -> D = E


end
end StatMech.FrontierD
