import sympy.sets.sets
import Lemma.Bool.Ne.is.NotEq
open Bool


@[main]
private lemma main
  {n i' : ℕ}
  {x y y' : ℕ → ℝ}
-- given
  (h₀ : i' ∈ range n)
  (h₁ : ∀ i ∈ range n, x i ≤ y i)
  (h₂ : ∀ i ∈ range n, y' i = if i = i' then x i else y i) :
-- imply
  ∀ i ∈ range n, x i ≤ y' i := by
-- proof
  intro i h_In
  by_cases h : i = i'
  ·
    rw [h]
    have := h₂ i' h₀
    simp at this
    linarith
  ·
    have h := Ne.of.NotEq h
    have := h₂ i h_In
    simp [h] at this
    rw [this]
    exact h₁ i h_In


-- created on 2025-04-06
-- updated on 2025-05-10
