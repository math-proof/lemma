import sympy.Basic


@[main]
private lemma main
  {f : α → Prop}
  {A B : Set α}
-- given
  (h : ∀ e ∈ A ∪ B, f e) :
-- imply
  ∀ e ∈ A, f e := by
-- proof
  intro e he
  apply h
  exact Or.inl he


-- created on 2025-07-20
