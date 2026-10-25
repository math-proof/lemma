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
import Def.v1.Atlas.Buildings.code.BNPair.TKernel
set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
variable (bp : BNPair G M)


/-- $T$ is normal in $N$, since $T = \ker \pi$ as a subgroup of $N$. -/
instance BNPair.T_normal_in_N : (bp.T.subgroupOf bp.N).Normal := by
  rw [bp.T_subgroupOf_eq_ker]
  exact MonoidHom.normal_ker bp.π


