import sympy.Basic


@[main]
private lemma main
  {g : ℤ → Prop}
  {a b : ℤ}
-- given
  (h₁ : g (a - 1))
  (h₂ : ∀ k ∈ Finset.Ico a b, g k)
  (h₃ : a ≤ b) :
-- imply
  ∀ k ∈ Finset.Ico (a - 1) b, g k := by
-- proof
  have hset : Finset.Ico (a - 1) b = insert (a - 1) (Finset.Ico a b) := by
    ext k
    simp [Finset.mem_Ico]
    omega
  intro k hk
  rw [hset] at hk
  simp at hk
  obtain rfl | h := hk
  · exact h₁
  · exact h₂ k (by simp [Finset.mem_Ico, h])


-- created on 2019-03-12
