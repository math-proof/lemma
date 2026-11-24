module
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
public import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilityExample
public import Def.StatisticalMechanics.Code.Exact3D.ToyRG.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.Hierarchical.Part4
public import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part3
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackageExample

theorem hierarchicalStableWitness_fixedPoint_eq_zero :
    hierarchicalStableWitness.fixedPoint = (0 : Fin 1 → ℝ) := by
  have hmem := hierarchicalStableWitness.fixedPoint_mem
  unfold FiniteContraction.ClosedBall at hmem
  exact FiniteContraction.eq_of_l1Dist_eq_zero
    (le_antisymm hmem (FiniteContraction.l1Dist_nonneg _ _))


end FiniteWitnessPackageExample
end Exact3D
end StatMech
