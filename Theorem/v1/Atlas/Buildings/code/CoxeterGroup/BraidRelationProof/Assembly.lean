/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/Assembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.DihedralHelpers.Part2
open Finset BigOperators Real


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The braid relation for $e_s$: $(\sigma_s\sigma_t)^{m(s,t)} (e_s) = e_s$. -/
theorem rotation_power_e_s (M : CoxeterMatrix B) (s t : B)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    (fun w => sigma M s (sigma M t w))^[M.M s t] (e s) = e s := by
  sorry

/-- The braid relation for $e_t$: $(\sigma_s\sigma_t)^{m(s,t)} (e_t) = e_t$. -/
theorem rotation_power_e_t (M : CoxeterMatrix B) (s t : B)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    (fun w => sigma M s (sigma M t w))^[M.M s t] (e t) = e t := by
  sorry


omit [DecidableEq B] [Fintype B] in
/-- For $s \ne t$ and finite $m(s,t)$, the matrix entry satisfies
$B_{s,t}^2 < 1$. -/
theorem formVal_sq_lt_one (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    formVal M s t ^ 2 < 1 := by
  sorry

omit [DecidableEq B] [Fintype B] in
/-- $1 - B_{s,t}^2 \ne 0$, so the orthogonal projection used below is
well-defined. -/
theorem one_sub_formVal_sq_ne_zero (M : CoxeterMatrix B) (s t : B)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    1 - formVal M s t ^ 2 ≠ 0 := by
  linarith [formVal_sq_lt_one M s t hst hm]

end CoxeterGroup
