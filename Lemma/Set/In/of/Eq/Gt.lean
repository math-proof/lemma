import sympy.Basic


@[path]
private lemma main
  {A s : Set ℤ}
  {e : ℤ}
-- given
  (h₀ : {e} ∩ s = A)
  (h₁ : 0 < A.ncard) :
-- imply
  e ∈ s := by
-- proof
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (Nat.pos_iff_ne_zero.mp h₁)
  rw [← h₀, Set.mem_inter_iff, Set.mem_singleton_iff] at hx
  exact hx.1 ▸ hx.2


-- created on 2021-04-01
