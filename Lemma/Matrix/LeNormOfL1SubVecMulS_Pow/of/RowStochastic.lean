import sympy.stats.stochastic_process_types
import Lemma.Matrix.LeNormOfL1SubVecMulS.of.RowStochastic
open Matrix
open scoped Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {Q : Matrix S S ℝ}
-- given
  (hQ : RowStochastic Q)
  (n : ℕ)
  (x y : S → ℝ) :
-- imply
  ‖ofL1 (x ᵥ* Q ^ n - y ᵥ* Q ^ n)‖ ≤ ‖ofL1 (x - y)‖ := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [pow_succ, ← Matrix.vecMul_vecMul]
    exact (@Matrix.LeNormOfL1SubVecMulS.of.RowStochastic _ _ _ hQ (x ᵥ* Q ^ n) (y ᵥ* Q ^ n)).trans ih


-- created on 2026-09-19
