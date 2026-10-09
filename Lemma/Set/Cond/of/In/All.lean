import sympy.Basic


@[path]
private lemma main
  {β : Type*}
  [One β]
  {b : α}
  {A : Set α}
  {f : α → β}
-- given
  (hb : b ∈ A)
  (h : ∀ a ∈ A, f a = 1) :
-- imply
  f b = 1 := by
-- proof
  exact h b hb


-- created on 2021-02-24
