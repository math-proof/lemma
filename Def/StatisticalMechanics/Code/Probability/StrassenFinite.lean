/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/StrassenFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.StrassenFull.Part7
import Structure.StatisticalMechanics.Code.Probability.StrassenFinite
open Finset
open scoped NNReal


namespace StatMech

namespace Probability

variable {P : Type*}


section Defs

variable [Fintype P]


def StochasticDom [Preorder P] (μ ν : P → NNReal) : Prop :=
  ∀ U : Finset P, (∀ ⦃a b⦄, a ≤ b → a ∈ U → b ∈ U) → ∑ x ∈ U, μ x ≤ ∑ x ∈ U, ν x

end Defs
end Probability
end StatMech
