import sympy.Basic


@[main]
private lemma main
  [CommRing α]
  {x h : ℕ → α}
  {c : α}
-- given
  (hrec : ∀ n, x (n + 1) = x n * c + h n) :
-- imply
  ∀ n, x n = x 0 * c ^ n + ∑ k ∈ Finset.range n, h k * c ^ (n - k - 1) := by
-- proof
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [hrec n, ih]
    have hsum :
        (∑ k ∈ Finset.range n, h k * c ^ (n - k - 1)) * c =
          ∑ k ∈ Finset.range n, h k * c ^ (n + 1 - k - 1) := by
      rw [Finset.sum_mul, Finset.sum_congr rfl]
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      rw [mul_assoc, ← pow_succ]
      have hke : n - k - 1 + 1 = n + 1 - k - 1 := by omega
      rw [hke]
    rw [add_mul, hsum]
    simp [Finset.sum_range_succ, pow_succ]
    ring


-- created on 2021-09-29
-- updated on 2023-06-17
