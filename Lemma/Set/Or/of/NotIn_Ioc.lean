import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {e a b : α}
-- given
  (h : e ∉ Ioc a b) :
-- imply
  e ≤ a ∨ e > b := by
-- proof
  rw [Set.mem_Ioc, not_and_or] at h
  cases h with
  | inl h1 =>
    left
    simp_all
  | inr h2 =>
    right
    simp_all


-- created on 2025-09-29
