import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M₀ : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddAbove (f '' S))
  (h : sSup (f '' S) ≥ M₀) :
-- imply
  ∀ M < M₀, ∃ x ∈ S, f x > M := by
-- proof
  intro M hM
  by_contra hn
  push Not at hn
  have hall : ∀ z ∈ f '' S, z ≤ M := by
    rintro z ⟨x, hx, rfl⟩
    exact hn x hx
  have hsle : sSup (f '' S) ≤ M := csSup_le (h₀.image f) hall
  linarith


-- created on 2019-04-11
