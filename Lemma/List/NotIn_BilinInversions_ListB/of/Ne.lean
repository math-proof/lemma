import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.InversionSet
open Finset BigOperators CoxeterGroup


private lemma sigma_e_other_t_component
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  (hst : s ≠ t) :
  sigma M s (e t) t = 1 := by
  rw [sigma_e_other]
  simp [e, hst]

/--
[t_not_in_bilinInversions_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionSet.lean)
-/
@[path]
private lemma main
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t) :
-- imply
  t ∉ bilinInversions M [s] := by
-- proof
  simp only [bilinInversions, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  change 0 ≤ sigma M s (e t) t
  rw [sigma_e_other_t_component hst]
  norm_num


-- created on 2026-10-24
