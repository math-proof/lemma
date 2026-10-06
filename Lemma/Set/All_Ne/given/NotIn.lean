import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set α}
  {y : α}
-- given
  (h : ∀ x ∈ S, x ≠ y) :
-- imply
  y ∉ S := by
-- proof
  intro hy
  exact h y hy rfl


-- created on 2021-01-14
