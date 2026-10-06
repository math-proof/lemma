import sympy.Basic


@[main]
private lemma main
  {g f h : α → Prop}
-- given
  (h₀ : ∀ e, g e → f e)
  (h₁ : ∀ e, g e → h e) :
-- imply
  ∀ e, g e → f e ∧ h e :=
-- proof
  fun e he => ⟨h₀ e he, h₁ e he⟩


-- created on 2018-11-30
