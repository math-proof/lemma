import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ModularForms.MeromorphicAtCusps
open scoped UpperHalfPlane MatrixGroups
open ModularFunction


/--
[IsMeromorphicAtCusps.at_infty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/MeromorphicAtCusps.lean)
-/
@[path]
private lemma IsMeromorphicAtCusps_at_infty_eq
  {f : ℍ → ℂ}
-- given
  (hf : IsMeromorphicAtCusps f) :
-- imply
  IsMeromorphicAtInfty f := by
-- proof
  apply ModularFunction.IsMeromorphicAtCusps.at_infty hf


-- created on 2026-10-20
