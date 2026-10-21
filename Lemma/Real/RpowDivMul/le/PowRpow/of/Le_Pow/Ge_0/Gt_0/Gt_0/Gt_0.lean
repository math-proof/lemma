import Mathlib
import sympy.Basic


/--
[roth_ridout_rpow_fraction_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (Q x μ : ℝ)
  (r n : ℕ)
-- given
  (hQ : 0 < Q)
  (hx : 0 < x)
  (hr : 0 < r)
  (hμ : 0 ≤ μ)
  (hbase : Q ≤ x ^ r) :
-- imply
  Real.rpow Q (μ * (n : ℝ) / r) ≤ (Real.rpow x μ) ^ n := by
-- proof
  have hexp : 0 ≤ μ * (n : ℝ) / r := by positivity
  calc
    _ ≤ Real.rpow (x ^ r) (μ * (n : ℝ) / r) :=
      Real.rpow_le_rpow hQ.le hbase hexp
    _ = Real.rpow (Real.rpow x (r : ℝ)) (μ * (n : ℝ) / r) := by
      congr 1
      exact (Real.rpow_natCast x r).symm
    _ = Real.rpow x ((r : ℝ) * (μ * (n : ℝ) / r)) :=
      (Real.rpow_mul hx.le _ _).symm
    _ = Real.rpow x (μ * n) := by
      congr 1
      field_simp
    _ = Real.rpow (Real.rpow x μ) (n : ℝ) := Real.rpow_mul hx.le _ _
    _ = (Real.rpow x μ) ^ n := Real.rpow_natCast _ _


-- created on 2026-10-21
