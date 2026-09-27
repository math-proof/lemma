import sympy.Basic


@[main]
private lemma main
  {S : Set α}
  {f : α → ℝ}
  {M : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : ∀ x ∈ S, f x ≤ M) :
-- imply
  sSup (f '' S) ≤ M := by
-- proof
  apply csSup_le (h₀.image f)
  rintro _ ⟨x, hx, rfl⟩
  exact h₁ x hx


-- created on 2026-09-26
