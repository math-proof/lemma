import sympy.matrices.confluent_vandermonde
import sympy.Basic
open Finset Nat


@[main]
private lemma vandermonde
  {d m : ℕ}
  {x : ℝ}
-- given
  (h : d ≤ m) :
-- imply
  ((Matrix.of fun (i : Fin d) (j : Fin m) => (j : ℝ) ^ (i : ℕ) * x ^ (j : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin d) => (-x) ^ ((j : ℤ) - (i : ℕ)) * ((j : ℕ).choose i : ℝ))).det =
    x ^ (d.choose 2) * ∏ i ∈ Finset.range d, (i ! : ℝ) := by
-- proof
  have hA : (Matrix.of fun (i : Fin d) (j : Fin m) => (j : ℝ) ^ (i : ℕ) * x ^ (j : ℕ)) =
      Matrix.of fun (i : Fin d) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + 0) ^ (i : ℕ) := by
    ext i j
    simp [mul_comm]
  rw [hA]
  exact Vandermonde.det_left h


-- created on 2022-01-15
