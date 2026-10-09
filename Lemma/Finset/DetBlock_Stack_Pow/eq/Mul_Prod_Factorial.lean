import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetOfVecCons_FunPow.eq.MulPowSub1Prod
open Matrix Finset Nat


@[path]
private lemma vandermonde
  {n : ℕ} {r : ℝ}
-- given
  (_h : n > 0) :
-- imply
  (Matrix.of (Matrix.vecCons (fun j : Fin (n + 1) => r ^ (j : ℕ)) (fun (i : Fin n) (j : Fin (n + 1)) => (j : ℝ) ^ (i : ℕ)))).det =
    (1 - r) ^ n * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
-- proof
  exact DetOfVecCons_FunPow.eq.MulPowSub1Prod


-- created on 2021-10-04
