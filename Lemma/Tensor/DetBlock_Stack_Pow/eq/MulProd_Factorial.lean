import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetOfVecCons2_FunPow.eq.MulMulMulPowSProd
open Matrix Finset Nat


@[main]
private lemma vandermonde.n2
  {n : ℕ}
  {r : ℝ}
-- given
  (_h : n > 0) :
-- imply
  (Matrix.of (Matrix.vecCons (fun j : Fin (n + 2) => r ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 2) => (j : ℝ) * r ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 2)) => (j : ℝ) ^ (i : ℕ))))).det =
    r * (1 - r) ^ (2 * n) * ∏ j ∈ Finset.range n, (j ! : ℝ) := by
-- proof
  have := DetOfVecCons2_FunPow.eq.MulMulMulPowSProd (n := n) (x₁ := r) (x₂ := 1)
  simp only [one_pow, mul_one] at this
  linear_combination this


-- created on 2026-09-27
