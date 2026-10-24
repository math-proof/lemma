import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.Basic
open Finset BigOperators CoxeterGroup


namespace Definitions
end Definitions
/--
[formVal_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Basic.lean)
-/
@[path]
private lemma formVal_symm_eq
  {M : CoxeterMatrix B}
  {s t : B} :
-- imply
  formVal M s t = formVal M t s := by
-- proof
  apply CoxeterGroup.formVal_symm M s t

/--
[formVal_diag](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Basic.lean)
-/
@[path]
private lemma formVal_diag_eq
  {M : CoxeterMatrix B}
  {s : B} :
-- imply
  formVal M s s = 1 := by
-- proof
  apply CoxeterGroup.formVal_diag M s

/--
[bilinForm_e_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Basic.lean)
-/
@[path]
private lemma bilinForm_e_e_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B} :
-- imply
  bilinForm M (e s) (e t) = formVal M s t := by
-- proof
  apply CoxeterGroup.bilinForm_e_e M s t

/--
[sigma_e_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Basic.lean)
-/
@[path]
private lemma sigma_e_self_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B} :
-- imply
  sigma M s (e s) = fun t => -(e s t) := by
-- proof
  apply CoxeterGroup.sigma_e_self M s


-- created on 2026-10-24
