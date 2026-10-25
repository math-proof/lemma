import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.InversionSet
open Finset BigOperators CoxeterGroup


/--
[mem_bilinInversions_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionSet.lean)
-/
@[path]
private lemma main
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {s : B} :
-- imply
  s ∈ bilinInversions M word ↔ wordSigma M word (e s) s < 0 := by
-- proof
  simp [bilinInversions]


-- created on 2026-10-24
