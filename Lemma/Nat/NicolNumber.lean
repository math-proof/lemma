import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NicolNumber
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[IsTNicolNumber.isNicolNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NicolNumber.lean)
-/
@[path]
lemma IsTNicolNumber.isNicolNumber
  {t n : ℕ}
-- given
  (h : IsTNicolNumber t n) :
-- imply
  IsNicolNumber n := by
-- proof
  refine ⟨h.1, ⟨t, ?_⟩⟩
  simpa [Nat.mul_comm] using h.2

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
