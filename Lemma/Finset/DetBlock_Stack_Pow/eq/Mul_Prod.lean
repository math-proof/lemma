import sympy.matrices.confluent_vandermonde
import sympy.Basic
open Finset Nat


@[main]
private lemma vandermonde.ratio
  {m d : ℕ} {r : ℝ}
-- given
  (h : m > d) :
-- imply
  (Matrix.of fun (a j : Fin m) => if (a : ℕ) < d then (j : ℝ) ^ (a : ℕ) * r ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - d)).det =
    r ^ (d.choose 2) * (1 - r) ^ (d * (m - d)) * (∏ i ∈ Finset.range d, (i ! : ℝ)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
-- proof
  exact Vandermonde.det_ratio h


-- created on 2026-09-27
