import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma rsolve
  {x : ℕ → ℝ}
  {c : ℝ}
  {h : ℕ → ℝ}
-- given
  (hr : ∀ n, x (n + 1) = x n * c + h n) :
-- imply
  ∀ n, x n = x 0 * c ^ n + ∑ k < n, h k * c ^ (n - k - 1) := by
-- proof
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hsplit : ∑ k < n + 1, h k * c ^ (n + 1 - k - 1) = ∑ k < n, h k * c ^ (n + 1 - k - 1) + h n * c ^ (n + 1 - n - 1) := by
      simpa only [Nat.Iio_eq_range] using Finset.sum_range_succ (fun k => h k * c ^ (n + 1 - k - 1)) n
    rw [hr n, ih, hsplit]
    have e : ∀ k < n, h k * c ^ (n - k - 1) * c = h k * c ^ (n + 1 - k - 1) := by
      intro k hk
      rw [mul_assoc, ← pow_succ, show n - k - 1 + 1 = n + 1 - k - 1 by omega]
    have e' : ∑ k < n, h k * c ^ (n - k - 1) * c = ∑ k < n, h k * c ^ (n + 1 - k - 1) :=
      Finset.sum_congr rfl (fun k hk => e k (by simpa using hk))
    rw [add_mul, Finset.sum_mul, e', show n + 1 - n - 1 = 0 by omega, pow_zero, pow_succ]
    ring


-- created on 2021-07-31
