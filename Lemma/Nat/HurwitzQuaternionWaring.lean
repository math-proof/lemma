import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.HurwitzQuaternionWaring
open MetaMathlibExt


/--
[hurwitz_quaternion_waring_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HurwitzQuaternionWaring.lean)
-/
@[path]
private lemma hurwitz_quaternion_waring_bound_eq
  {ℓ : ℕ}
-- given
  (hℓpos : 0 < ℓ)
  (hℓmod : ℓ % 3 = 1 ∨ ℓ % 3 = 2) :
-- imply
  let IsHurwitz : Quaternion ℚ → Prop := by
-- proof
  apply MetaMathlibExt.hurwitz_quaternion_waring_bound ℓ hℓpos hℓmod


-- created on 2026-10-20
