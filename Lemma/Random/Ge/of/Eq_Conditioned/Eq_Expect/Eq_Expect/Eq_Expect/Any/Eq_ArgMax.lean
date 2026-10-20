import Mathlib.Algebra.Order.BigOperators.Group.Finset
import sympy.Basic
open Finset


/--
An argmax action beats every policy mixture: if `i` maximises `Q`, then `∑ π a * Q a ≤ Q i`.
-/
@[path]
private lemma drift
  [Fintype ι] [Nonempty ι]
  {π Q : ι → ℝ}
  {i : ι}
-- given
  (h₀ : ∀ a, 0 ≤ π a)
  (h₁ : ∑ a, π a = 1)
  (h₂ : ∀ j, Q j ≤ Q i) :
-- imply
  ∑ a, π a * Q a ≤ Q i := by
-- proof
  calc
    _ ≤ ∑ a, π a * Q i := by
      refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h₂ a) (h₀ a)
    _ = Q i := by rw [← sum_mul, h₁, one_mul]


-- created on 2026-10-11
-- updated on 2026-10-20
