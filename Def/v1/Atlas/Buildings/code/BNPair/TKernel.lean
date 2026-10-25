/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/TKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
variable (bp : BNPair G M)


/-- The action of $N$ on the standard apartment $W$ by left translation: $n \cdot w =
\pi(n) \cdot w$. -/
def BNPair.apartmentActionFun (n : bp.N) (w : M.Group) : M.Group :=
  bp.π n * w

