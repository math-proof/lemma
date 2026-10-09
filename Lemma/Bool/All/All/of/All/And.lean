import sympy.Basic


@[path]
private lemma main
  {g f h : α → Prop}
-- given
  (h₀ : ∀ e, g e → f e ∧ h e) :
-- imply
  (∀ e, g e → f e) ∧ ∀ e, g e → h e :=
-- proof
  ⟨fun e he => (h₀ e he).1, fun e he => (h₀ e he).2⟩


-- created on 2018-11-30
