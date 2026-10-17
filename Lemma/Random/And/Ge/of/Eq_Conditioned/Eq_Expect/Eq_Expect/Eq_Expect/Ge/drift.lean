import Mathlib.Algebra.Order.BigOperators.Group.Finset
import sympy.Basic
open Finset


/--
Myopic policy comparison: every mixture of action values is at most the best action.
-/
@[path]
private lemma main
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
  have hB : BddAbove (Set.range Q) := (Set.finite_range Q).bddAbove
  have hsup : ⨆ a, Q a = Q i :=
    le_antisymm (ciSup_le h₂) (le_ciSup hB i)
  calc
    _ ≤ ∑ a, π a * Q i := by
      refine sum_le_sum fun a _ => ?_
      exact mul_le_mul_of_nonneg_left (h₂ a) (h₀ a)
    _ = (∑ a, π a) * Q i := by rw [← sum_mul]
    _ = Q i := by rw [h₁, one_mul]


-- created on 2026-10-11
-- updated on 2026-10-17
