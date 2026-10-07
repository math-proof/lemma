import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetOf.eq.MulPowSProdProd.of.Le
import Lemma.Matrix.DetOfVecCons2_FunPow.eq.MulMulMulPowSProd
import Lemma.Matrix.DetOfVecCons_FunPow.eq.MulMulPowSProd
open Matrix Finset Nat


@[main]
private lemma vandermonde.n2
  {n : ℕ} {x₁ x₂ : ℝ}
-- given
  (_h₀ : x₂ ≠ 0)
  (_h₁ : n ≥ 1) :
-- imply
  (Matrix.of (Matrix.vecCons (fun j : Fin (n + 2) => x₁ ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 2) => (j : ℝ) * x₁ ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 2)) => (j : ℝ) ^ (i : ℕ) * x₂ ^ (j : ℕ))))).det =
    x₁ * x₂ ^ (n.choose 2) * (x₂ - x₁) ^ (2 * n) * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
-- proof
  exact DetOfVecCons2_FunPow.eq.MulMulMulPowSProd


@[main]
private lemma vandermonde.mn
  {x₁ x₂ : ℝ}
  {m d : ℕ}
-- given
  (_h₀ : x₂ ≠ 0)
  (h₁ : m > d) :
-- imply
  (Matrix.of fun (a j : Fin m) =>
      if (a : ℕ) < d then (j : ℝ) ^ (a : ℕ) * x₁ ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - d) * x₂ ^ (j : ℕ)).det =
    x₂ ^ ((m - d).choose 2) * x₁ ^ (d.choose 2) * (x₂ - x₁) ^ (d * (m - d)) *
      (∏ i ∈ Finset.range d, (i ! : ℝ)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
-- proof
  exact DetOf.eq.MulPowSProdProd.of.Le (by omega)


@[main]
private lemma vandermonde.n1
  {n : ℕ} {x₁ x₂ : ℝ}
-- given
  (_h₀ : x₁ ≠ 0)
  (_h₁ : n ≥ 1) :
-- imply
  (Matrix.of (Matrix.vecCons (fun j : Fin (n + 1) => x₂ ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 1)) => (j : ℝ) ^ (i : ℕ) * x₁ ^ (j : ℕ)))).det =
    x₁ ^ (n.choose 2) * (x₁ - x₂) ^ n * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
-- proof
  exact DetOfVecCons_FunPow.eq.MulMulPowSProd


-- created on 2026-09-27
