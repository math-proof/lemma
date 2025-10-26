import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {p : ℕ → Prop}
-- given
  (h₀ : ∀ i ∈ range n, p i)
  (a : ℕ) :
-- imply
  ∀ i ∈ Finset.Ico a n, p i := by
-- proof
  intro i hi
  have h_Lt : i < n := by
    -- Extract the upper bound from the interval membership
    rw [Finset.mem_Ico] at hi
    linarith
  have h_In : i ∈ range n := by
    simp [h_Lt]
  exact h₀ i h_In


-- created on 2025-04-26
-- updated on 2025-04-26
