import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {p : α → Prop} :
-- imply
  (∀ x ∈ A, p x) ↔ ∀ x, x ∉ A ∨ p x := by
-- proof
  simp only [imp_iff_not_or]


-- created on 2018-12-23
