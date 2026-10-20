import sympy.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {x : α}
  {A B : Set α}
-- given
  (h₀ : p → x ∈ A)
  (h₁ : ¬p → x ∈ B) :
-- imply
  x ∈ if p then A else B := by
-- proof
  if hp : p then
    simpa [hp] using h₀ hp
  else
    simpa [hp] using h₁ hp


-- created on 2018-09-23
-- updated on 2026-10-17
