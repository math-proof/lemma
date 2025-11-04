import Lemma.Bool.Ne.is.NotEq
open Bool


@[main]
private lemma main
  [DecidableEq ι]
  {i' : ι}
  {x y y' : ι → ℝ}
  {s : Finset ι}
-- given
  (h₀ : i' ∈ s)
  (h₁ : ∀ i ∈ s, x i ≤ y i)
  (h₂ : ∀ i ∈ s, y' i = if i = i' then x i else y i) :
-- imply
  ∀ i ∈ s, x i ≤ y' i := by
-- proof
  intro i h_In
  if h : i = i' then
    rw [h]
    have := h₂ i' h₀
    simp at this
    linarith
  else
    have h := Ne.of.NotEq h
    have := h₂ i h_In
    simp [h] at this
    rw [this]
    exact h₁ i h_In


-- created on 2025-04-06
-- updated on 2025-05-10
