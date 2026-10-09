import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetOf.eq.MulPowSProdProd.of.Le
open Matrix Nat


@[path]
private lemma main
  {n : ℕ}
  {x₁ x₂ : ℝ} :
-- imply
  (Matrix.of (Matrix.vecCons (fun j : Fin (n + 2) => x₁ ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 2) => (j : ℝ) * x₁ ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 2)) => (j : ℝ) ^ (i : ℕ) * x₂ ^ (j : ℕ))))).det =
    x₁ * x₂ ^ (n.choose 2) * (x₂ - x₁) ^ (2 * n) * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
-- proof
  have hM : Matrix.of (Matrix.vecCons (fun j : Fin (n + 2) => x₁ ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 2) => (j : ℝ) * x₁ ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 2)) => (j : ℝ) ^ (i : ℕ) * x₂ ^ (j : ℕ)))) =
      Matrix.of fun (a j : Fin (n + 2)) => if (a : ℕ) < 2 then (j : ℝ) ^ (a : ℕ) * x₁ ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - 2) * x₂ ^ (j : ℕ) := by
    ext a j
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a <;> simp
  rw [hM, DetOf.eq.MulPowSProdProd.of.Le (by omega), show (2 : ℕ).choose 2 = 1 by decide, show n + 2 - 2 = n by omega,
    show ∏ i ∈ Finset.range 2, (i ! : ℝ) = 1 by norm_num [Finset.prod_range_succ]]
  ring


-- created on 2026-10-07
