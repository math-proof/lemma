import sympy.Basic


@[path]
private lemma main
  {e : α}
  {A B : Set α}
-- given
  (h : e ∈ A ∩ B) :
-- imply
  e ∈ A ∧ e ∈ B := by
-- proof
  exact h


-- created on 2018-09-22
