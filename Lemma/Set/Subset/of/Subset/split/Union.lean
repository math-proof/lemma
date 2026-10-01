import sympy.Basic


@[main]
private lemma main
  {A B S : Set α}
-- given
  (h : A ∪ B ⊆ S) :
-- imply
  A ⊆ S :=
-- proof
  fun _ hx => h (Or.inl hx)


-- created on 2020-07-28
