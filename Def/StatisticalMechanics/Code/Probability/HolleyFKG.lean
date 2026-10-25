/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HolleyFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.StrassenFinite.Part2
import Mathlib.Combinatorics.SetFamily.FourFunctions
open Finset
open scoped NNReal


namespace StatMech

namespace Probability

variable {α : Type*}


section Conditions

def HolleyLatticeCondition [Lattice α] (μ₁ μ₂ : α → ℝ≥0) : Prop :=
  ∀ x y, μ₁ x * μ₂ y ≤ μ₁ (x ⊓ y) * μ₂ (x ⊔ y)


def FKGCondition [Lattice α] (μ : α → ℝ≥0) : Prop :=
  ∀ x y, μ x * μ y ≤ μ (x ⊓ y) * μ (x ⊔ y)


end Conditions
end Probability
end StatMech
