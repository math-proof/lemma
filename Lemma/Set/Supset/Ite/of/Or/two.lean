import sympy.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {A B S : Set α}
-- given
  (h₀ : p → S ⊆ A)
  (h₁ : ¬p → S ⊆ B) :
-- imply
  S ⊆ if p then A else B := by
-- proof
  if hp : p then
    simpa [hp] using h₀ hp
  else
    simpa [hp] using h₁ hp


-- created on 2026-10-11
-- updated on 2026-10-17
