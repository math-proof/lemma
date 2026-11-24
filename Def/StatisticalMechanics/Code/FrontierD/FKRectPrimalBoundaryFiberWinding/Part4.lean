module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleMergeWinding
public import Theorem.StatisticalMechanics.Code.FrontierD.PermCycleQuotientWeightSum
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding.Part4
open Equiv Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectPrimalClusterNonzeroBoundaryCycles
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    Finset (FKRectConfigurationBlackBoundaryCycle R omega) := by
  classical
  exact Finset.univ.filter fun C =>
    fkRectBlackBoundaryCycleInPrimalCluster R omega x C ∧
      fkRectBlackBoundaryCycleWinding R omega C ≠ 0

end
end StatMech.FrontierD
