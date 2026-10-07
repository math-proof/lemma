import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetOf.eq.MulPowSProdProd.of.Le
open Matrix Nat


@[main]
private lemma main
  {n : ℕ}
  {r : ℝ} :
-- imply
  (Matrix.of (Matrix.vecCons (fun j : Fin (n + 4) => r ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) * r ^ (j : ℕ))
      (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) ^ 2 * r ^ (j : ℕ))
      (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) ^ 3 * r ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 4)) => (j : ℝ) ^ (i : ℕ))))))).det =
    12 * r ^ Nat.choose 4 2 * (1 - r) ^ (4 * n) * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
-- proof
  have hM : Matrix.of (Matrix.vecCons (fun j : Fin (n + 4) => r ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) * r ^ (j : ℕ))
      (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) ^ 2 * r ^ (j : ℕ))
      (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) ^ 3 * r ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 4)) => (j : ℝ) ^ (i : ℕ)))))) =
      Matrix.of fun (a j : Fin (n + 4)) => if (a : ℕ) < 4 then (j : ℝ) ^ (a : ℕ) * r ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - 4) * (1 : ℝ) ^ (j : ℕ) := by
    ext a j
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a) a) a <;>
      simp [Nat.mod_eq_of_lt (show 2 < n + 4 by omega), Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]
  rw [hM, DetOf.eq.MulPowSProdProd.of.Le (by omega), show n + 4 - 4 = n by omega,
    show ∏ i ∈ Finset.range 4, (i ! : ℝ) = 12 by norm_num [Finset.prod_range_succ, Nat.factorial]]
  ring


-- created on 2026-10-07
