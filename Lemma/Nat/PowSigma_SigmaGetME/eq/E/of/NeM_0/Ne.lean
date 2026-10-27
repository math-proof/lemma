import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.Assembly.Part2
open Finset BigOperators Real CoxeterGroup


namespace Definitions
end Definitions
/--
[rotation_power_e_s](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/Assembly.lean)
-/
@[path]
private lemma rotation_power_e_s_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t)
  (hm : M.M s t ≠ 0) :
-- imply
  (fun w => sigma M s (sigma M t w))^[M.M s t] (e s) = e s := by
-- proof
  apply CoxeterGroup.rotation_power_e_s M s t hst hm

/--
[rotation_power_e_t](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/Assembly.lean)
-/
@[path]
private lemma rotation_power_e_t_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t)
  (hm : M.M s t ≠ 0) :
-- imply
  (fun w => sigma M s (sigma M t w))^[M.M s t] (e t) = e t := by
-- proof
  apply CoxeterGroup.rotation_power_e_t M s t hst hm

/--
[formVal_sq_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/Assembly.lean)
-/
@[path]
private lemma formVal_sq_lt_one_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t)
  (hm : M.M s t ≠ 0) :
-- imply
  formVal M s t ^ 2 < 1 := by
-- proof
  apply CoxeterGroup.formVal_sq_lt_one M s t hst hm

/--
[one_sub_formVal_sq_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/Assembly.lean)
-/
@[path]
private lemma one_sub_formVal_sq_ne_zero_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t)
  (hm : M.M s t ≠ 0) :
-- imply
  1 - formVal M s t ^ 2 ≠ 0 := by
-- proof
  apply CoxeterGroup.one_sub_formVal_sq_ne_zero M s t hst hm

/--
[decomp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/Assembly.lean)
-/
@[path]
private lemma decomp_eq_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ} :
-- imply
  v = decompAlpha M s t v • e s + decompBeta M s t v • e t + decompW M s t v := by
-- proof
  apply CoxeterGroup.decomp_eq M s t v

/--
[decomp_ortho_s](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/Assembly.lean)
-/
@[path]
private lemma decomp_ortho_s_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hm : M.M s t ≠ 0) :
-- imply
  bilinForm M (decompW M s t v) (e s) = 0 := by
-- proof
  apply CoxeterGroup.decomp_ortho_s M s t v hst hm

/--
[decomp_ortho_t](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/Assembly.lean)
-/
@[path]
private lemma decomp_ortho_t_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hm : M.M s t ≠ 0) :
-- imply
  bilinForm M (decompW M s t v) (e t) = 0 := by
-- proof
  apply CoxeterGroup.decomp_ortho_t M s t v hst hm

/--
[braid_power_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/Assembly.lean)
-/
@[path]
private lemma braid_power_ne_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hm : M.M s t ≠ 0) :
-- imply
  (fun w => sigma M s (sigma M t w))^[M.M s t] v = v := by
-- proof
  apply CoxeterGroup.braid_power_ne M s t hst hm v


-- created on 2026-10-24
