import sympy.Basic


@[path]
private lemma limits.restrict
  [Preorder α]
  {a b c : α}
  {f : α → Prop}
-- given
  (h₀ : c < b)
  (h₁ : ∀ x ∈ Set.Ico a b, f x) :
-- imply
  ∀ x ∈ Set.Icc a c, f x :=
-- proof
  fun x hx => h₁ x ⟨hx.1, lt_of_le_of_lt hx.2 h₀⟩


-- created on 2026-09-27
