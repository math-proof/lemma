import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetOfVecCons3_FunPow.eq.MulMulMul2Pow3PowSub1Prod
open Matrix Finset Nat


@[path]
private lemma vandermonde.n3
  {n : ℕ} {r : ℝ}
-- given
  (_h : n > 0) :
-- imply
  (Matrix.of (Matrix.vecCons (fun j : Fin (n + 3) => r ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 3) => (j : ℝ) * r ^ (j : ℕ))
      (Matrix.vecCons (fun j : Fin (n + 3) => (j : ℝ) ^ 2 * r ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 3)) => (j : ℝ) ^ (i : ℕ)))))).det =
    2 * r ^ 3 * (1 - r) ^ (3 * n) * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
-- proof
  exact DetOfVecCons3_FunPow.eq.MulMulMul2Pow3PowSub1Prod


-- created on 2026-09-27
