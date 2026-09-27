import Mathlib.Logic.Function.Iterate
import Lemma.Matrix.SmatAsOperator.eq.ToLp1VecMulOfLp.of.Simplex
open WithLp Matrix Function


@[main]
private lemma main
  {S : Type u} [Fintype S] [DecidableEq S]
  {P : Matrix S S ℝ} [RowStochastic P]
-- given
  (n : ℕ)
  (μ : Simplex S) :
-- imply
  ((smat_as_operator P)^[n] μ : l1Space S) = WithLp.toLp 1 (WithLp.ofLp (μ : l1Space S) ᵥ* (P ^ n)) := by
-- proof
  induction n generalizing μ with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', Matrix.SmatAsOperator.eq.ToLp1VecMulOfLp.of.Simplex, ih]
    simp [pow_succ, Matrix.vecMul_vecMul]


-- created on 2026-09-22
-- updated on 2026-09-23
