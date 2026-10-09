import sympy.Basic


@[path]
private lemma main
  {A B : Set α}
  {f : α → Prop} :
-- imply
  (∀ x ∈ A, f x) ∧ (∀ x ∈ B, f x) ↔ ∀ x ∈ A ∪ B, f x := by
-- proof
  simp only [Set.mem_union, or_imp, forall_and]


-- created on 2019-05-07
