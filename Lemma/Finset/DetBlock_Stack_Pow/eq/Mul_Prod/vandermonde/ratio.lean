import Mathlib.Data.Nat.Factorial.Basic
import Lemma.Matrix.DetOf.eq.MulPowSProdProd.of.Le
import sympy.Basic
open Matrix


@[path]
private lemma main
  {d m : ℕ}
  {r : ℝ}
-- given
  (h₀ : d < m) :
-- imply
  (Matrix.of fun (a j : Fin m) =>
      if (a : ℕ) < d then (j : ℝ) ^ (a : ℕ) * r ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - d)).det =
    r ^ (d.choose 2) * (1 - r) ^ (d * (m - d)) *
      (∏ i ∈ Finset.range d, (Nat.factorial i : ℝ)) * ∏ i ∈ Finset.range (m - d), (Nat.factorial i : ℝ) := by
-- proof
  have h := DetOf.eq.MulPowSProdProd.of.Le (x₁ := r) (x₂ := (1 : ℝ)) (d := d) (m := m) (by omega)
  simpa [one_pow, one_mul, mul_one] using h


-- created on 2026-10-11
-- updated on 2026-10-17
