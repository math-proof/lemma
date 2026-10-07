import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetOf.eq.MulPowSProdProd.of.Gt
open Matrix Finset Nat


@[main]
private lemma vandermonde.ratio
  {m d : ℕ} {r : ℝ}
-- given
  (h : m > d) :
-- imply
  (Matrix.of fun (a j : Fin m) => if (a : ℕ) < d then (j : ℝ) ^ (a : ℕ) * r ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - d)).det =
    r ^ (d.choose 2) * (1 - r) ^ (d * (m - d)) * (∏ i ∈ Finset.range d, (i ! : ℝ)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
-- proof
  exact DetOf.eq.MulPowSProdProd.of.Gt h


-- created on 2026-09-27
