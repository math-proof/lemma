import sympy.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {a b : α}
  {S : Set α}
-- given
  (h₀ : ({a, b} : Set α) ⊆ S) :
-- imply
  (if p then a else b) ∈ S := by
-- proof
  if hp : p then
    simpa [hp] using h₀ (by simp)
  else
    simpa [hp] using h₀ (by simp)


-- created on 2026-10-11
-- updated on 2026-10-17
