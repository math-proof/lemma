/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/StrassenFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.StrassenFull.Part7
open Finset
open scoped NNReal


namespace StatMech

namespace Probability

variable {P : Type*}


section Defs

variable [Fintype P]


structure IsCoupling [PartialOrder P] (μ ν : P → ℝ≥0) (π : P × P → ℝ≥0) : Prop where
  
  fst_marginal : ∀ x, ∑ y, π (x, y) = μ x
  
  snd_marginal : ∀ y, ∑ x, π (x, y) = ν y


structure IsMonotoneCoupling [PartialOrder P] (μ ν : P → ℝ≥0) (π : P × P → ℝ≥0) : Prop
    extends IsCoupling μ ν π where
  
  supported : ∀ x y, ¬ x ≤ y → π (x, y) = 0


end Defs
end Probability
end StatMech
