import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetMulOfMulPowOfPowNegChoose.eq.MulMulPowPowSubProd
open Matrix Finset Nat


@[main]
private lemma vandermonde.col_transform
  {m d : ℕ} {x δ l : ℝ} :
-- imply
  ((Matrix.of fun (i : Fin (m - d)) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0))).det =
    x ^ ((m - d).choose 2) * (x - l) ^ (d * (m - d)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
-- proof
  exact DetMulOfMulPowOfPowNegChoose.eq.MulMulPowPowSubProd


-- created on 2026-09-27
