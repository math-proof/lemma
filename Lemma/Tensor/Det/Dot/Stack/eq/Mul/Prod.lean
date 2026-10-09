import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetMulOfOfPowNegChoose.eq.MulPowProd.of.Le
open Matrix Nat


@[path]
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
  exact DetMulOfOfPowNegChoose.eq.MulPowProd.of.Le h


-- created on 2022-01-15
