import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Nat.BinetClosedForm


namespace MetaMathlibExt

/--
[jacobsthal_closedForm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/JacobsthalClosedForm.lean)
-/
@[path]
lemma jacobsthal_closedForm
  {J : ℕ → ℕ}
  {m : ℕ}
-- given
  (h_zero : J 0 = 1)
  (h_one : J 1 = 1)
  (h_rec : ∀ n : ℕ, J (n + 2) = J (n + 1) + 2 * J n) :
-- imply
  (J m : ℚ) = ((2 : ℚ) ^ (m + 1) + (-1 : ℚ) ^ m) / 3 := by
-- proof
  have h := MetaMathlibExt.binet_closed_form_second_order
    (u := fun n => (J n : ℚ)) (P := 1) (Q := -2) (α := 2) (β := -1) (n := m)
    (by norm_num) (by norm_num) (by norm_num) (fun n => by simp [h_rec n])
  simp only [h_zero, h_one] at h
  rw [h, pow_succ]
  ring

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-28
