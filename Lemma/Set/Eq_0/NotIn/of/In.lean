import sympy.Basic


@[path]
private lemma main
  {e : α} {s : Set α} [Decidable (e ∈ s)]
-- given
  (h₀ : e ∈ s) :
-- imply
  decide (e ∉ s) = false := by
-- proof
  simp [h₀]


-- created on 2021-03-10
-- updated on 2026-10-17
