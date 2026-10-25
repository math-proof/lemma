import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import Lemma.Matrix.MulOfMulPowOfPowNegChoose.eq.MulOfChooseSumOf
open Matrix


@[path]
private lemma main
  [Field R]
  {n m d : ℕ}
  {δ l : R} :
-- imply
  (Matrix.of fun (i : Fin n) (j : Fin m) => ((j : R) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : R) else 0)) =
    (Matrix.of fun (i j : Fin n) => ((i : ℕ).choose j : R) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : R) * (-l) ^ (d - h) * (h : R) ^ ((i : ℤ) - (j : ℕ))) *
    (Matrix.of fun (i : Fin n) (j : Fin (m - d)) => ((j : R) + δ) ^ (i : ℕ)) := by
-- proof
  simpa only [one_pow, one_mul, mul_one] using MulOfMulPowOfPowNegChoose.eq.MulOfChooseSumOf (n := n) (m := m) (d := d) (x := 1) (δ := δ) (l := l)


-- created on 2026-10-07
