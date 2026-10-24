import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ModularForms.MeromorphicAtCusps
open scoped UpperHalfPlane MatrixGroups
open ModularFunction


namespace ModularFunction

/--
[IsMeromorphicAtCusps.at_infty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/MeromorphicAtCusps.lean)
-/
@[path]
lemma IsMeromorphicAtCusps.at_infty
  {f : ℍ → ℂ}
-- given
  (hf : IsMeromorphicAtCusps f) :
-- imply
  IsMeromorphicAtInfty f := by
-- proof
  simpa using hf 1

end ModularFunction


-- created on 2026-10-20
-- updated on 2026-10-23
