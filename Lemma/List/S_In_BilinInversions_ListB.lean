import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.InversionSet
open Finset BigOperators CoxeterGroup


/--
[s_in_bilinInversions_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionSet.lean)
-/
@[path]
private lemma main
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B} :
-- imply
  s ∈ bilinInversions M [s] := by
-- proof
  simp only [bilinInversions, Finset.mem_filter, Finset.mem_univ, true_and]
  -- wordSigma M [s] (e s) s < 0
  change sigma M s (e s) s < 0
  rw [sigma_e_self]
  simp [e]


-- created on 2026-10-24
