import sympy.Basic


@[path]
private lemma main
  {s : Set α}
  {p : α → Prop}
-- given
  (h₀ : ∀ x ∈ s, p x) :
-- imply
  ∀ x ∈ s, p x ∧ s ≠ ∅ := by
-- proof
  intro x hx
  exact ⟨h₀ x hx, (Set.nonempty_of_mem hx).ne_empty⟩


-- created on 2026-10-11
-- updated on 2026-10-17
