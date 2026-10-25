/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpnessFull
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

section SelfImprovement

variable {V : Type*}


structure SimonLieb (τ : V → V → ℝ) (o : V) (S : Finset V)
    (simWeight : V → V → ℝ) (boundaryTargets : Finset V) : Prop where
  
  τ_nonneg : ∀ a b, 0 ≤ τ a b
  
  weight_nonneg : ∀ x y, 0 ≤ simWeight x y
  
  simon : ∀ z, z ∉ S →
    τ o z ≤ ∑ x ∈ S, ∑ y ∈ boundaryTargets, simWeight x y * τ y z


end SelfImprovement
end Sharpness
end StatMech
