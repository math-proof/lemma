import sympy.matrices.confluent_vandermonde
import sympy.Basic
open Finset Nat


@[main]
private lemma vandermonde.n2
  {n : ℕ} {x₁ x₂ : ℝ}
-- given
  (_h : n ≥ 1) :
-- imply
  (Matrix.of (Matrix.vecCons (fun j : Fin (n + 2) => x₁ ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 2) => (j : ℝ) * x₁ ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 2)) => (j : ℝ) ^ (i : ℕ) * x₂ ^ (j : ℕ))))).det =
    x₁ * x₂ ^ (n.choose 2) * (x₂ - x₁) ^ (2 * n) * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
-- proof
  exact Vandermonde.det_n2


@[main]
private lemma vandermonde.n1
  {n : ℕ} {x₁ x₂ : ℝ}
-- given
  (_h : n ≥ 1) :
-- imply
  (Matrix.of (Matrix.vecCons (fun j : Fin (n + 1) => x₂ ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 1)) => (j : ℝ) ^ (i : ℕ) * x₁ ^ (j : ℕ)))).det =
    x₁ ^ (n.choose 2) * (x₁ - x₂) ^ n * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
-- proof
  exact Vandermonde.det_n1


-- created on 2026-09-27
