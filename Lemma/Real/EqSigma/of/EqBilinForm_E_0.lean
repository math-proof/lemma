import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelation
open Finset BigOperators CoxeterGroup


/--
[sigma_fixes_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelation.lean)
-/
@[path]
private lemma sigma_fixes_orthogonal_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {v : B → ℝ}
-- given
  (h : bilinForm M v (e s) = 0) :
-- imply
  sigma M s v = v := by
-- proof
  apply CoxeterGroup.sigma_fixes_orthogonal M s v h

/--
[sigma_comp_fixes_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelation.lean)
-/
@[path]
private lemma sigma_comp_fixes_orthogonal_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ}
-- given
  (hs : bilinForm M v (e s) = 0)
  (ht : bilinForm M v (e t) = 0) :
-- imply
  sigma M s (sigma M t v) = v := by
-- proof
  apply CoxeterGroup.sigma_comp_fixes_orthogonal M s t v hs ht

/--
[sigma_comp_e_s](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelation.lean)
-/
@[path]
private lemma sigma_comp_e_s_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B} :
-- imply
  sigma M s (sigma M t (e s)) = fun u => (4 * formVal M s t ^ 2 - 1) * e s u - 2 * formVal M s t * e t u := by
-- proof
  apply CoxeterGroup.sigma_comp_e_s M s t

/--
[sigma_comp_e_t](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelation.lean)
-/
@[path]
private lemma sigma_comp_e_t_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B} :
-- imply
  sigma M s (sigma M t (e t)) = fun u => 2 * formVal M s t * e s u - e t u := by
-- proof
  apply CoxeterGroup.sigma_comp_e_t M s t


-- created on 2026-10-23
