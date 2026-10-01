import sympy.matrices.confluent_vandermonde
import sympy.Basic
open Finset Nat


@[main]
private lemma vandermonde
  {m d : ℕ}
  {x₁ x₂ : ℝ}
-- given
  (h : m > d + 1) :
-- imply
  (Matrix.of fun (a j : Fin m) =>
      if (a : ℕ) < d then (j : ℝ) ^ (a : ℕ) * x₁ ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - d) * x₂ ^ (j : ℕ)).det =
    x₂ ^ ((m - d).choose 2) * x₁ ^ (d.choose 2) * (x₂ - x₁) ^ (d * (m - d)) *
      (∏ i ∈ Finset.range d, (i ! : ℝ)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
-- proof
  exact Vandermonde.confluent_det (by omega)


-- created on 2022-07-11
