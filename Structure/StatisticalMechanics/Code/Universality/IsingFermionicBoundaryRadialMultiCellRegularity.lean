/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Mathlib.Algebra.Order.Chebyshev
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part2


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


structure MeshUniformCompactHolder (F : Nat → Complex → Complex) where
  holder : ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
    ∃ constant exponent : NNReal, 0 < exponent ∧
      ∀ n, HolderOnWith constant exponent (F n) K

end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
