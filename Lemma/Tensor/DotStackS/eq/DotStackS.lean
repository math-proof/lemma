import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import Lemma.Matrix.MulOfPowAddOfPowNegChoose.eq.MulOfChooseSumOf
open Matrix


@[path]
private lemma vandermonde_col_transform
  {n m d : ℕ} {δ l : ℝ} :
-- imply
  (Matrix.of fun (i : Fin n) (j : Fin m) => ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0)) =
    (Matrix.of fun (i j : Fin n) => ((i : ℕ).choose j : ℝ) *
      ∑ h < (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * (h : ℝ) ^ ((i : ℤ) - (j : ℕ))) *
    (Matrix.of fun (i : Fin n) (j : Fin (m - d)) => ((j : ℝ) + δ) ^ (i : ℕ)) :=
-- proof
  MulOfPowAddOfPowNegChoose.eq.MulOfChooseSumOf


-- created on 2026-09-27
-- updated on 2026-11-21
