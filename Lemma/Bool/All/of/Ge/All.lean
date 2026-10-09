import sympy.Basic


@[path]
private lemma limits.restrict
  [Preorder α]
  {a b c : α}
  {f : α → Prop}
-- given
  (h₀ : c ≥ a)
  (h₁ : ∀ x ∈ Set.Icc a b, f x) :
-- imply
  ∀ x ∈ Set.Icc c b, f x :=
-- proof
  fun x hx => h₁ x ⟨le_trans h₀ hx.1, hx.2⟩


-- created on 2026-09-27
