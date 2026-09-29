import sympy.matrices.confluent_vandermonde
import sympy.Basic
open Finset Nat


@[main]
private lemma vandermonde.col_transform
  {m d : ℕ} {x δ l : ℝ} :
-- imply
  ((Matrix.of fun (i : Fin (m - d)) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0))).det =
    x ^ ((m - d).choose 2) * (x - l) ^ (d * (m - d)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
-- proof
  exact Vandermonde.det_x


-- created on 2026-09-27
