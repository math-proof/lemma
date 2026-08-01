import sympy.Basic


@[main]
private lemma main
  {x : α}
  {A B : Set α}
-- given
  (h : x ∈ A ∩ B) :
-- imply
  x ∈ A ∧ x ∈ B := by
-- proof
  simp_all


-- created on 2018-09-22
