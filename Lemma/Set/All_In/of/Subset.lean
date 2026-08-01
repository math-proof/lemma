import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : B ⊆ A) :
-- imply
  ∀ a ∈ B, a ∈ A := by
-- proof
  assumption


-- created on 2018-03-30
