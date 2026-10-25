/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/Assembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.DihedralHelpers.Part2
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.Assembly.Part2
open Finset BigOperators Real


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The braid relation hypothesis holds on the geometric representation: for
every pair $s, t$ with finite Coxeter order, $(\sigma_s\sigma_t)^{m(s,t)}$ is
the identity on $\mathbb{R}^B$. -/
noncomputable def braidRelationHyp (M : CoxeterMatrix B) : BraidRelationHyp M where
  braid_power_eq_one := by
    intro s t hm v
    by_cases hst : s = t
    · subst hst
      have hm1 : M.M s s = 1 := M.diagonal s
      simp [sigma_involution]
    · exact braid_power_ne M s t hst hm v

end CoxeterGroup
