import sympy.Basic


@[main]
private lemma main
  {n k : ℕ}
-- given
  (h : k > 0) :
-- imply
  (n.choose k : ℝ) = n / k * (n - 1).choose (k - 1) := by
-- proof
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  cases n with
  | zero =>
    simp
  | succ n =>
    have h' : ((n + 1).choose (k + 1) : ℝ) * (k + 1) = (n + 1) * n.choose k := by
      exact_mod_cast (Nat.add_one_mul_choose_eq n k).symm
    simp only [Nat.add_sub_cancel]
    rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
    push_cast
    linarith


@[main]
private lemma decrease
  {n k : ℕ}
-- given
  (h : k < n) :
-- imply
  (n.choose k : ℝ) = (n - 1).choose k / ((n : ℝ) - k) * n := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hk : k ≤ m + 1 := by omega
  have h' := congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_mul_succ_eq m k)
  push_cast [Nat.cast_sub hk] at h'
  have hlt : (k : ℝ) < m + 1 := by exact_mod_cast h
  have hne : (m : ℝ) + 1 - k ≠ 0 := by
    intro h0
    linarith
  simp only [Nat.add_sub_cancel]
  push_cast
  rw [div_mul_eq_mul_div, eq_div_iff hne]
  linarith


@[main]
private lemma increase
  {n k : ℕ}
-- given
  (h : k < n) :
-- imply
  (n.choose k : ℝ) = (n + 1).choose k / ((n : ℝ) + 1) * ((n : ℝ) + 1 - k) := by
-- proof
  have hk : k ≤ n + 1 := by omega
  have h' := congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_mul_succ_eq n k)
  push_cast [Nat.cast_sub hk] at h'
  push_cast
  rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
  linarith


-- created on 2026-09-27
