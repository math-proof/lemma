/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
public import Mathlib.Algebra.Order.Chebyshev
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part2


namespace StatMech.Universality

open Filter Metric Set

public noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


structure MeshUniformCompactHolder (F : Nat → Complex → Complex) where
  holder : ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
    ∃ constant exponent : NNReal, 0 < exponent ∧
      ∀ n, HolderOnWith constant exponent (F n) K

end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
