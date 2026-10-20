import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NicolNumber
open scoped BigOperators
open MetaMathlibExt


/--
[IsTNicolNumber.isNicolNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NicolNumber.lean)
-/
@[path]
private lemma IsTNicolNumber_isNicolNumber_eq
  {t n : ℕ}
-- given
  (h : IsTNicolNumber t n) :
-- imply
  IsNicolNumber n := by
-- proof
  apply MetaMathlibExt.IsTNicolNumber.isNicolNumber h


-- created on 2026-10-20
