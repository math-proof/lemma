import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.OesperWeavingDeterminant
open scoped BigOperators Matrix
open MetaMathlibExt


/--
[oesper_weaving_three_determinant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/OesperWeavingDeterminant.lean)
-/
@[path]
private lemma oesper_weaving_three_determinant_eq
  {k : Nat}
-- given
  (hk : 0 < k) :
-- imply
  let C : Nat -> Int := by
-- proof
  apply MetaMathlibExt.oesper_weaving_three_determinant k hk


-- created on 2026-10-20
