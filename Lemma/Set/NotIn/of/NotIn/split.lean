import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : α}
  {A B : Set α}
-- given
  (h : x ∉ A ∪ B) :
-- imply
  x ∉ A := by
-- proof
  intro hx
  exact h (Or.inl hx)


-- created on 2021-06-09
