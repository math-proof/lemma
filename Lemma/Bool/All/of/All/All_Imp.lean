import sympy.Basic


@[main]
private lemma main
  {x : ι → α}
  {p q : α → Prop}
-- given
  (h₀ : ∀ t : α, p t → q t)
  (h₁ : ∀ i : ι, p (x i)) :
-- imply
  ∀ i : ι, q (x i) := by
-- proof
  intro i
  apply h₀ (x i)
  apply h₁ i


-- created on 2025-04-06
-- updated on 2025-04-26
