import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetOf.eq.MulPowSProdProd.of.Le
open Matrix Nat


@[path]
private lemma main
  {m d : ℕ}
  {r : ℝ}
-- given
  (h : m > d) :
-- imply
  (Matrix.of fun (a j : Fin m) => if (a : ℕ) < d then (j : ℝ) ^ (a : ℕ) * r ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - d)).det =
    r ^ (d.choose 2) * (1 - r) ^ (d * (m - d)) * (∏ i ∈ Finset.range d, (i ! : ℝ)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
-- proof
  have := DetOf.eq.MulPowSProdProd.of.Le (d := d) (m := m) (x₁ := r) (x₂ := 1) (by omega)
  simp only [one_pow, mul_one, one_mul] at this
  rw [this]


-- created on 2026-10-07
