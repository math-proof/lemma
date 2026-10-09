import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetOf.eq.MulPowSProdProd.of.Le
open Matrix Nat


@[path]
private lemma main
  {n : ℕ}
  {r : ℝ} :
-- imply
  (Matrix.of (Matrix.vecCons (fun j : Fin (n + 1) => r ^ (j : ℕ)) (fun (i : Fin n) (j : Fin (n + 1)) => (j : ℝ) ^ (i : ℕ)))).det =
    (1 - r) ^ n * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
-- proof
  have hM : Matrix.of (Matrix.vecCons (fun j : Fin (n + 1) => r ^ (j : ℕ)) (fun (i : Fin n) (j : Fin (n + 1)) => (j : ℝ) ^ (i : ℕ))) =
      Matrix.of fun (a j : Fin (n + 1)) => if (a : ℕ) < 1 then (j : ℝ) ^ (a : ℕ) * r ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - 1) * (1 : ℝ) ^ (j : ℕ) := by
    ext a j
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  rw [hM, DetOf.eq.MulPowSProdProd.of.Le (by omega), show (1 : ℕ).choose 2 = 0 by decide, show n + 1 - 1 = n by omega,
    show ∏ i ∈ Finset.range 1, (i ! : ℝ) = 1 by norm_num [Finset.prod_range_succ]]
  ring


-- created on 2026-10-07
