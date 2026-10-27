import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
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


-- created on 2019-05-15
-- updated on 2026-10-26
