import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {x : α}
  {A B : Set α}
-- given
  (h₀ : p → x ∉ A)
  (h₁ : ¬p → x ∉ B) :
-- imply
  x ∉ if p then A else B := by
-- proof
  if hp : p then
    simpa [hp] using h₀ hp
  else
    simpa [hp] using h₁ hp


-- created on 2021-06-12
-- updated on 2026-10-26
