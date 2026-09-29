import Mathlib.RingTheory.Binomial
import Mathlib.Data.Nat.Choose.Central
import sympy.sets.sets
import sympy.Basic
open Nat


@[main]
private lemma half
  {n : ℕ} :
-- imply
  Ring.choose (1 / 2 : ℝ) n = -(-1 / 4) ^ n * ((2 * n).choose n : ℝ) / (2 * n - 1) := by
-- proof
  have key : ∀ m : ℕ, Ring.choose (1 / 2 : ℝ) m = (m ! : ℝ)⁻¹ * ∏ j ∈ Finset.range m, ((1 / 2 : ℝ) - j) := by
    intro m
    rw [Ring.choose_eq_smul, ← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, descPochhammer_map, descPochhammer_eval_eq_prod_range, smul_eq_mul]
  have claim : ∀ m : ℕ, (2 * (m : ℝ) - 1) * ∏ j ∈ Finset.range m, ((1 / 2 : ℝ) - j) = -(-1 / 4) ^ m * (m.centralBinom : ℝ) * (m ! : ℝ) := by
    intro m
    induction m with
    | zero => norm_num
    | succ n ih =>
      have hc := congrArg (Nat.cast : ℕ → ℝ) (Nat.succ_mul_centralBinom_succ n)
      push_cast at hc
      rw [Finset.prod_range_succ, Nat.factorial_succ]
      push_cast
      linear_combination (-(2 * (n : ℝ) + 1) / 2) * ih + ((-1 / 4 : ℝ) ^ (n + 1) * (n ! : ℝ)) * hc
  have h1 : (2 * (n : ℝ) - 1) ≠ 0 := by
    intro e
    have e2 : (2 * n : ℝ) = 1 := by linarith
    norm_cast at e2
    omega
  have h5 : (n ! : ℝ) ≠ 0 := by positivity
  rw [key, ← Nat.centralBinom_eq_two_mul_choose, eq_div_iff h1]
  rw [show (n ! : ℝ)⁻¹ * (∏ j ∈ Finset.range n, ((1 / 2 : ℝ) - j)) * (2 * n - 1) = (n ! : ℝ)⁻¹ * ((2 * n - 1) * ∏ j ∈ Finset.range n, ((1 / 2 : ℝ) - j)) by ring, claim n]
  rw [mul_comm, mul_assoc, mul_inv_cancel₀ h5, mul_one]


-- created on 2026-09-27
