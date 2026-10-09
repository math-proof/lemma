import sympy.Basic


@[path]
private lemma main
  [Preorder α]
  {a b c : α}
  {f : α → Prop}
-- given
  (h₀ : c > a)
  (h₁ : ∀ x ∈ Set.Ioc a b, f x) :
-- imply
  ∀ x ∈ Set.Icc c b, f x :=
-- proof
  fun x hx => h₁ x ⟨lt_of_lt_of_le h₀ hx.1, hx.2⟩


-- created on 2019-07-11
