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
import Structure.StatisticalMechanics.Code.Sharpness.IsingSharpnessFull
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

section SelfImprovement

variable {V : Type*}


noncomputable def simonConst (S : Finset V) (simWeight : V → V → ℝ) (boundaryTargets : Finset V) :
    ℝ := ∑ x ∈ S, ∑ y ∈ boundaryTargets, simWeight x y


end SelfImprovement
end Sharpness
end StatMech
