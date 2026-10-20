import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → α}
  {S : Set α}
  {σ : Equiv.Perm (Fin n)}
-- given
  (h₀ : ∀ k, x k ∈ S) :
-- imply
  ∀ k, x (σ k) ∈ S := by
-- proof
  intro k
  exact h₀ (σ k)


-- created on 2020-11-04
-- updated on 2026-10-17
