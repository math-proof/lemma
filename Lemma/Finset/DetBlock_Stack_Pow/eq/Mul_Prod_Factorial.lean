import sympy.matrices.confluent_vandermonde
import sympy.Basic
open Finset Nat


@[main]
private lemma vandermonde
  {n : ℕ} {r : ℝ}
-- given
  (_h : n > 0) :
-- imply
  (Matrix.of (Matrix.vecCons (fun j : Fin (n + 1) => r ^ (j : ℕ)) (fun (i : Fin n) (j : Fin (n + 1)) => (j : ℝ) ^ (i : ℕ)))).det =
    (1 - r) ^ n * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
-- proof
  exact Vandermonde.det_cons_pow


-- created on 2021-10-04
