import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetOfVecCons4_FunPow.eq.MulMulMul12PowChoosePowSub1Prod
open Matrix Finset Nat


@[main]
private lemma vandermonde.n4
  {n : ℕ} {r : ℝ}
-- given
  (_h : n > 0) :
-- imply
  (Matrix.of (Matrix.vecCons (fun j : Fin (n + 4) => r ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) * r ^ (j : ℕ))
      (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) ^ 2 * r ^ (j : ℕ))
      (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) ^ 3 * r ^ (j : ℕ)) (fun (i : Fin n) (j : Fin (n + 4)) => (j : ℝ) ^ (i : ℕ))))))).det =
    12 * r ^ (Nat.choose 4 2) * (1 - r) ^ (4 * n) * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
-- proof
  exact DetOfVecCons4_FunPow.eq.MulMulMul12PowChoosePowSub1Prod


-- created on 2026-09-27
