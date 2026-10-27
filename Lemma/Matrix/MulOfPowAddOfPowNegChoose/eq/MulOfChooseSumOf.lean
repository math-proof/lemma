import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import Lemma.Matrix.MulOfMulPowOfPowNegChoose.eq.MulOfChooseSumOf
import Syntax.LinearAlgebra.Matrix.Notation
open Matrix


@[path]
private lemma main
  [Field R]
  {n m d : ℕ}
  {δ l : R} :
-- imply
  ([i < n, j < m] ((j : R) + δ) ^ (i : ℕ)) *
    ([i < m, j < m - d]
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : R) else 0)) =
    ([i < n, j < n] (((i : ℕ).choose j : R) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : R) * (-l) ^ (d - h) * (h : R) ^ ((i : ℤ) - (j : ℕ)))) *
    ([i < n, j < m - d] ((j : R) + δ) ^ (i : ℕ)) := by
-- proof
  simpa only [one_pow, one_mul, mul_one] using MulOfMulPowOfPowNegChoose.eq.MulOfChooseSumOf (n := n) (m := m) (d := d) (x := 1) (δ := δ) (l := l)


-- created on 2026-10-07
-- updated on 2026-10-27
