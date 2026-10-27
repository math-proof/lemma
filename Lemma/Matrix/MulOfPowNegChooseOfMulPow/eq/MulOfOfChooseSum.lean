import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import Lemma.Matrix.MulOfMulPowOfPowNegChoose.eq.MulOfChooseSumOf
import Syntax.LinearAlgebra.Matrix.Notation
open Matrix


@[path]
private lemma main
  {n m d : ℕ}
  {x δ l : ℝ} :
-- imply
  ([i < m - d, j < m]
      (-l) ^ ((d : ℤ) + (i : ℕ) - (j : ℕ)) * (if (i : ℕ) ≤ j then (d.choose ((j : ℕ) - i) : ℝ) else 0)) *
    ([i < m, j < n] x ^ (i : ℕ) * ((i : ℝ) + δ) ^ (j : ℕ)) =
    ([i < m - d, j < n] ((i : ℝ) + δ) ^ (j : ℕ) * x ^ (i : ℕ)) *
    ([i < n, j < n] (((j : ℕ).choose i : ℝ) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h * (h : ℝ) ^ ((j : ℤ) - (i : ℕ)))) := by
-- proof
  have := congrArg Matrix.transpose (MulOfMulPowOfPowNegChoose.eq.MulOfChooseSumOf (n := n) (m := m) (d := d) (x := x) (δ := δ) (l := l))
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at this
  convert this using 2 <;> (ext a b; rfl)


-- created on 2026-10-07
-- updated on 2026-10-27
