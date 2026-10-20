import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.BinetClosedForm
open MetaMathlibExt


/--
[binet_closed_form_second_order](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinetClosedForm.lean)
-/
@[path]
private lemma binet_closed_form_second_order_eq
  [Field K]
  {u : ℕ → K}
  {P Q α β : K}
  {n : ℕ}
-- given
  (hα : α ^ 2 - P * α + Q = 0)
  (hβ : β ^ 2 - P * β + Q = 0)
  (hne : α ≠ β)
  (hrec : ∀ n : ℕ, u (n + 2) = P * u (n + 1) - Q * u n) :
-- imply
  u n = ((u 1 - β * u 0) * α ^ n - (u 1 - α * u 0) * β ^ n) / (α - β) := by
-- proof
  apply MetaMathlibExt.binet_closed_form_second_order u P Q α β hα hβ hne hrec n


-- created on 2026-10-20
