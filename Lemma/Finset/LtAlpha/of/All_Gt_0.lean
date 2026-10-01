import sympy.concrete.continued_fraction_tail
import sympy.concrete.continuant_shift
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i ≥ 1, x i > 0) :
-- imply
  alpha ((List.range (2 * n - 1)).map x) < alpha ((List.range (2 * n + 1)).map x) := by
-- proof
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by omega]
  have hp : ∀ m, ∀ j, 1 ≤ j → j < m → 0 < x j := fun _ j hj _ => h j hj
  rw [alpha_eq_of_tail_pos x (by omega) (hp _), alpha_eq_of_tail_pos x (by omega) (hp _)]
  have hK1 := K_pos_of x (2 * k + 1) (by omega) (hp _)
  have hK2 := K_pos_of x (2 * k + 1 + 2) (by omega) (hp _)
  have d : H x (2 * k + 1 + 1) * K x (2 * k + 1) - H x (2 * k + 1) * K x (2 * k + 1 + 1) = 1 := by
    rw [HK_det x (2 * k + 1), show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, neg_one_sq, one_pow]
  have key : H x (2 * k + 1 + 2) * K x (2 * k + 1) - H x (2 * k + 1) * K x (2 * k + 1 + 2) = x (2 * k + 1 + 1) := by
    show (H x (2 * k + 1 + 1) * x (2 * k + 1 + 1) + H x (2 * k + 1)) * K x (2 * k + 1) -
      H x (2 * k + 1) * (K x (2 * k + 1 + 1) * x (2 * k + 1 + 1) + K x (2 * k + 1)) = _
    linear_combination x (2 * k + 1 + 1) * d
  rw [div_lt_div_iff₀ hK1 hK2]
  linarith [h (2 * k + 1 + 1) (by omega)]


-- created on 2026-09-27
