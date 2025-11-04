import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
  {A : Set α}

-- given
  (h : ∀ x ∈ A, p x)
  (x : α):
-- imply
  p x ∨ x ∉ A := by
-- proof
  grind


-- created on 2025-04-27
-- updated on 2025-07-29
