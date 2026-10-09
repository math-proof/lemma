import sympy.Basic
import Mathlib.LinearAlgebra.Vandermonde
open Matrix


@[path]
private lemma vandermonde
  [CommRing α]
  {n : ℕ}
  {a : Fin n → α} :
-- imply
  (Matrix.of fun (i j : Fin n) => a j ^ (i : ℕ)).det = ∏ i : Fin n, ∏ j ∈ Finset.Iio i, (a i - a j) := by
-- proof
  rw [← Matrix.det_transpose]
  have h : (Matrix.of fun (i j : Fin n) => a j ^ (i : ℕ))ᵀ = Matrix.vandermonde a := by
    ext i j
    simp [Matrix.vandermonde]
  rw [h, Matrix.det_vandermonde]
  exact Finset.prod_comm' (by intro x y; simp)


-- created on 2020-08-21
