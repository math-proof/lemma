import sympy.matrices.confluent_vandermonde
import sympy.Basic
open Finset Nat


@[main]
private lemma vandermonde
  {n : ℕ} {r : ℝ} :
-- imply
  (Matrix.of fun (a j : Fin n) => if (a : ℕ) = 0 then 1 - r ^ ((j : ℕ) + 1) else ((j : ℝ) + 1) ^ (a : ℕ)).det =
    (1 - r) ^ n * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
-- proof
  exact Vandermonde.det_powAdd


-- created on 2020-10-14
