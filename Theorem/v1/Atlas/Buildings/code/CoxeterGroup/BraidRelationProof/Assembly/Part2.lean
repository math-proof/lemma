/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/Assembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.DihedralHelpers.Part2
import Def.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.Assembly
open Finset BigOperators Real


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The decomposition identity:
$v = \alpha e_s + \beta e_t + w$. -/
theorem decomp_eq (M : CoxeterMatrix B) (s t : B) (v : B → ℝ) :
    v = decompAlpha M s t v • e s + decompBeta M s t v • e t + decompW M s t v := by
  simp only [decompW]
  ext u; simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- The component $w$ is $B$-orthogonal to $e_s$. -/
theorem decomp_ortho_s (M : CoxeterMatrix B) (s t : B) (v : B → ℝ)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    bilinForm M (decompW M s t v) (e s) = 0 := by
  simp only [decompW]
  have heq : v - decompAlpha M s t v • e s - decompBeta M s t v • e t =
    v + (- decompAlpha M s t v) • e s + (- decompBeta M s t v) • e t := by
    ext u; simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [heq, bilinForm_add_left, bilinForm_add_left, bilinForm_smul_left, bilinForm_smul_left,
      bilinForm_e_e, bilinForm_e_e, formVal_diag, formVal_symm M t s]
  simp only [decompAlpha, decompBeta]
  have hne := one_sub_formVal_sq_ne_zero M s t hst hm
  field_simp; ring

/-- The component $w$ is $B$-orthogonal to $e_t$. -/
theorem decomp_ortho_t (M : CoxeterMatrix B) (s t : B) (v : B → ℝ)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    bilinForm M (decompW M s t v) (e t) = 0 := by
  simp only [decompW]
  have heq : v - decompAlpha M s t v • e s - decompBeta M s t v • e t =
    v + (- decompAlpha M s t v) • e s + (- decompBeta M s t v) • e t := by
    ext u; simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [heq, bilinForm_add_left, bilinForm_add_left, bilinForm_smul_left, bilinForm_smul_left,
      bilinForm_e_e, bilinForm_e_e, formVal_diag]
  simp only [decompAlpha, decompBeta]
  have hne := one_sub_formVal_sq_ne_zero M s t hst hm
  field_simp; ring


/-- For $s \ne t$ with finite Coxeter order $m(s,t)$, the geometric
representation satisfies the braid relation $(\sigma_s \sigma_t)^{m(s,t)} v =
v$ on every vector $v$. -/
theorem braid_power_ne (M : CoxeterMatrix B) (s t : B)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) (v : B → ℝ) :
    (fun w => sigma M s (sigma M t w))^[M.M s t] v = v := by
  set α' := decompAlpha M s t v
  set β := decompBeta M s t v
  set w := decompW M s t v
  have hv : v = α' • e s + β • e t + w := decomp_eq M s t v
  have hws : bilinForm M w (e s) = 0 := decomp_ortho_s M s t v hst hm
  have hwt : bilinForm M w (e t) = 0 := decomp_ortho_t M s t v hst hm
  conv_lhs => rw [hv]
  rw [show α' • e s + β • e t + w = (α' • e s + β • e t) + w from by
    ext u; simp [Pi.add_apply, Pi.smul_apply]]
  rw [iterate_sigma_comp_add, iterate_sigma_comp_fixes_orthogonal M s t _ w hws hwt,
      iterate_sigma_comp_add, iterate_sigma_comp_smul, iterate_sigma_comp_smul,
      rotation_power_e_s M s t hst hm, rotation_power_e_t M s t hst hm, ← hv]

end CoxeterGroup
