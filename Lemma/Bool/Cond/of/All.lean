import sympy.Basic


@[main]
private lemma main
  [Nonempty α]
  {r : Prop}
-- given
  (h : ∀ _ : α, r) :
-- imply
  r := by
-- proof
  obtain ⟨x⟩ := ‹Nonempty α›
  exact h x


-- created on 2026-09-26
