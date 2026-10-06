import sympy.Basic


@[main]
private lemma main
  {a : α}
  {A B : Set α}
-- given
  (h : a ∈ A)
  (heq : B ∪ {a} = A) :
-- imply
  A \ {a} = B \ {a} := by
-- proof
  ext y
  rw [← heq]
  simp [Set.mem_union]


-- created on 2021-04-05
-- updated on 2023-06-22
