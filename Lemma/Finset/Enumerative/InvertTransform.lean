import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.InvertTransform
open MetaMathlibExt


/--
[invertTransform_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/InvertTransform.lean)
-/
@[path]
private lemma invertTransform_spec_eq
  {a : ℕ → ℤ} :
-- imply
  (1 - PowerSeries.X * PowerSeries.mk a) *
      (1 + PowerSeries.X * PowerSeries.mk (invertTransform a)) = 1 := by
-- proof
  apply MetaMathlibExt.invertTransform_spec a


-- created on 2026-10-20
