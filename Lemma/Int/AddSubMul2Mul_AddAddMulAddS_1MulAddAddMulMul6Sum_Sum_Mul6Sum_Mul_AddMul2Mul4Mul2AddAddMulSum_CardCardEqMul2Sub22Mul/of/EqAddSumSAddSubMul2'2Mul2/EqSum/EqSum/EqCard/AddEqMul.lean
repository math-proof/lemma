import Mathlib
import sympy.Basic
open scoped BigOperators


/--
[AlgebraicCurve_CellDissection_euler_count_grid](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_CellDissection_euler_count_grid.lean)
-/
@[path]
private lemma main
  [Fintype ιc] [Fintype ιp]
  {fib : ιc → Type*} [∀ b, Fintype (fib b)]
  {n J K np nc : ℕ} {g : ℤ}
  {ec : ∀ b, fib b → ℕ}
  {ep : ιp → ℕ}
-- given
  (hJK : np + nc = J * K)
  (hnc : Fintype.card ιc = nc)
  (hec : ∀ b, ∑ w, ec b w = n)
  (hep : ∑ q, ep q = n)
  (hRH : (∑ b, ∑ w, ((ec b w : ℤ) - 1)) + ∑ q, ((ep q : ℤ) - 1) = 2 * g - 2 + 2 * (n : ℤ)) :
-- imply
  2 * ((n : ℤ) * ((J + 1) * (K + 1) + J * K + K)) -
      ((6 * n * np : ℤ) + (∑ b, ∑ w, (6 * ec b w : ℤ)) + ∑ q, ((ep q : ℤ) * (2 * J + 4 * K))) +
      2 * ((n * np : ℤ) + (∑ b, (Fintype.card (fib b) : ℤ)) + Fintype.card ιp) =
    2 * (2 - 2 * g) := by
-- proof
  have hcap' : ∀ b : ιc, (∑ w, ((ec b w : ℤ) - 1)) = (n : ℤ) - Fintype.card (fib b) := by
    intro b
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum, hec b]
    simp
  have hinf' : (∑ q, ((ep q : ℤ) - 1)) = (n : ℤ) - Fintype.card ιp := by
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum, hep]
    simp
  have hS : (∑ b, ∑ w, ((ec b w : ℤ) - 1)) = (nc : ℤ) * n - ∑ b, (Fintype.card (fib b) : ℤ) := by
    simp only [hcap']
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hnc]
    simp
  have h6 : (∑ b, ∑ w, (6 * ec b w : ℤ)) = 6 * (n : ℤ) * nc := by
    have h6n : (∑ b, ∑ w, 6 * ec b w) = 6 * n * nc := by
      simp only [← Finset.mul_sum, hec, Finset.sum_const, Finset.card_univ, hnc, smul_eq_mul]
      ring
    exact_mod_cast h6n
  have hp : (∑ q, ((ep q : ℤ) * (2 * J + 4 * K))) = (n : ℤ) * (2 * J + 4 * K) := by
    rw [← Finset.sum_mul, ← Nat.cast_sum, hep]
  have hJK' : (np : ℤ) + nc = J * K := by
    exact_mod_cast hJK
  linear_combination (-4 * (n : ℤ)) * hJK' - 2 * hRH - h6 - hp + 2 * hS + 2 * hinf'


-- created on 2026-10-13
