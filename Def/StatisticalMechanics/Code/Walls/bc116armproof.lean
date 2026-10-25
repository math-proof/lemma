/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc114haschild.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc101mengergap
import Theorem.StatisticalMechanics.Code.Walls.bc116armproof
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*}

variable {G : SimpleGraph V}


def bc116_ThroughPathCovered (F : SimpleGraph V) (B H : V → Prop) : Prop :=
  ∀ v, ¬ B v → ¬ H v →
    ∃ (s t : V) (p : F.Walk s t), p.IsPath ∧ v ∈ p.support ∧ v ≠ s ∧ v ≠ t


end StatMech.Walls
