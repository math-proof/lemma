import Mathlib
import sympy.Basic
import Def.NumberTheory.SimsekNumber
open MetaMathlibExt


namespace MetaMathlibExt

/--
[simsekNumber_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SimsekNumber.lean)
-/
@[path]
lemma simsekNumber_eq_sum
  {n k : Nat}
  {lam : ℂ} :
-- imply
  simsekNumber n k lam =
      ((k.factorial : ℂ))⁻¹ *
        ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * (((j : ℂ) ^ n) * (lam ^ j)) :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[simsekNumber_zero_k](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SimsekNumber.lean)
-/
@[path]
lemma simsekNumber_zero_k
  {n : Nat}
  {lam : ℂ} :
-- imply
  simsekNumber n 0 lam = (0 : ℂ) ^ n := by
-- proof
  unfold simsekNumber
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[simsekNumber_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SimsekNumber.lean)
-/
@[path]
lemma simsekNumber_zero_zero
  {lam : ℂ} :
-- imply
  simsekNumber 0 0 lam = 1 := by
-- proof
  unfold simsekNumber
  simp

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
