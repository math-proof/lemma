import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.InversionSet
open Finset BigOperators CoxeterGroup


/--
[bilinInversions_nil](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionSet.lean)
-/
@[path]
private lemma main
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  bilinInversions M ([] : List B) = ∅ := by
-- proof
  simp only [bilinInversions, Finset.filter_eq_empty_iff]
  intro s _
  simp only [wordSigma_nil, not_lt]
  have : e s s = 1 := by simp [e]
  linarith


-- created on 2026-10-23
-- updated on 2026-10-26
