import Mathlib
import sympy.Basic
import sympy.functions.special.LambertWFunction


/--
[LambertWFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/LambertWFunction.lean)
-/
@[path]
private lemma exists_unique_lambert_map_preimage_is
-- given
  (x : ℝ)
  (hx : -Real.exp (-1) < x) :
-- imply
  ∃! y : Subtype (fun y : ℝ => -1 < y),
    MetaMathlibExt.lambertMap y.val = x := by
-- proof
  apply MetaMathlibExt.existsUnique_lambertMap_preimage x hx


-- created on 2026-10-11
