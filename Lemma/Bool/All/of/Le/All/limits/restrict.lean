import sympy.Basic


@[path]
private lemma main
  [Preorder α]
  {a b c : α}
  {f : α → Prop}
-- given
  (h₀ : c ≤ b)
  (h₁ : ∀ x ∈ Set.Icc a b, f x) :
-- imply
  ∀ x ∈ Set.Icc a c, f x :=
-- proof
  fun x hx => h₁ x ⟨hx.1, le_trans hx.2 h₀⟩


-- created on 2019-10-23
-- updated on 2026-10-17
