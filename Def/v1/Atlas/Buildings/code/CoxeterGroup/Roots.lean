/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Roots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.SigmaOrder
open Finset BigOperators


namespace CoxeterGroup

set_option linter.unusedSectionVars false

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- A vector $v : B \to \mathbb{R}$ is positive when $0 \le v(s)$ for every simple generator $s$. -/
def IsPositive (v : B → ℝ) : Prop := ∀ s, 0 ≤ v s

/-- A vector $v : B \to \mathbb{R}$ is negative when $v(s) \le 0$ for every simple generator $s$. -/
def IsNegative (v : B → ℝ) : Prop := ∀ s, v s ≤ 0

end CoxeterGroup
