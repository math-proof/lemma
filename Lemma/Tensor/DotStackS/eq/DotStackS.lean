import sympy.matrices.confluent_vandermonde
import sympy.Basic
open Finset Nat


@[main]
private lemma vandermonde.col_transform
  {n m d : ℕ} {δ l : ℝ} :
-- imply
  (Matrix.of fun (i : Fin n) (j : Fin m) => ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0)) =
    (Matrix.of fun (i j : Fin n) => ((i : ℕ).choose j : ℝ) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * (h : ℝ) ^ ((i : ℤ) - (j : ℕ))) *
    (Matrix.of fun (i : Fin n) (j : Fin (m - d)) => ((j : ℝ) + δ) ^ (i : ℕ)) := by
-- proof
  exact Vandermonde.col_transform_S


-- created on 2026-09-27
