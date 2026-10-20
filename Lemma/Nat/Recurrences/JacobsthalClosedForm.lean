import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.JacobsthalClosedForm
open MetaMathlibExt


/--
[jacobsthal_closedForm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/JacobsthalClosedForm.lean)
-/
@[path]
private lemma jacobsthal_closedForm_eq
  {J : ℕ → ℕ}
  {m : ℕ}
-- given
  (h_zero : J 0 = 1)
  (h_one : J 1 = 1)
  (h_rec : ∀ n : ℕ, J (n + 2) = J (n + 1) + 2 * J n) :
-- imply
  (J m : ℚ) = ((2 : ℚ) ^ (m + 1) + (-1 : ℚ) ^ m) / 3 := by
-- proof
  apply MetaMathlibExt.jacobsthal_closedForm J h_zero h_one h_rec m


-- created on 2026-10-20
