import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {v : Fin n → ℝ} :
-- imply
  (Matrix.vandermonde v).det = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j - v i) :=
-- proof
  Matrix.det_vandermonde v


-- created on 2020-10-03
-- updated on 2026-10-17
