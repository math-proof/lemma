import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.MulOfPowAddOfPowNegChoose.eq.Zero
open Matrix


@[main]
private lemma vandermonde.col_transformation
  {d m : ℕ} {x δ : ℝ} :
-- imply
  (Matrix.of fun (i : Fin d) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-x) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0)) = 0 := by
-- proof
  exact MulOfPowAddOfPowNegChoose.eq.Zero


-- created on 2026-09-27
