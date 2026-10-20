import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NormalNumber
open Real Filter
open MetaMathlibExt.NormalNumber


/--
[IsNormalInBase.isSimplyNormalInBase](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumber.lean)
-/
@[path]
private lemma IsNormalInBase_isSimplyNormalInBase_eq
  {b : ℕ}
  {x : ℝ}
-- given
  (h : IsNormalInBase b x) :
-- imply
  IsSimplyNormalInBase b x := by
-- proof
  apply MetaMathlibExt.NormalNumber.IsNormalInBase.isSimplyNormalInBase h


-- created on 2026-10-20
