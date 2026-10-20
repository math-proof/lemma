import sympy.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {A B S : Set α}
-- given
  (h₀ : p → A ⊆ S)
  (h₁ : ¬p → B ⊆ S) :
-- imply
  (if p then A else B) ⊆ S := by
-- proof
  if hp : p then
    simpa [hp] using h₀ hp
  else
    simpa [hp] using h₁ hp


-- created on 2021-06-13
-- updated on 2026-10-17
