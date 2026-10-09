import sympy.Basic


@[path]
private lemma main
  {n k : ℕ}
-- given
  (h₀ : 1 ≤ k)
  (h₁ : k < n) :
-- imply
  n.choose k = (n - 1).choose k + (n - 1).choose (k - 1) := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.choose_succ_succ, add_comm]


-- created on 2020-09-28
