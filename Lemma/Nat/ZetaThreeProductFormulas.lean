import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ZetaThreeProductFormulas
open MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen
open MetaMathlibExt


/--
[zeta_three_infinite_product_formulas](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ZetaThreeProductFormulas.lean)
-/
@[path]
private lemma zeta_three_infinite_product_formulas_eq
  :
-- imply
  Filter.Tendsto
    (fun m : ℕ =>
    ∏ n ∈ Finset.Icc 1 (2 * m + 1),
    (1 / Real.rpow (Real.exp 1) (1 / 4)) *
    (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^
    (((n * (n + 1) / 2 : ℕ) : ℤ) * (-1 : ℤ) ^ n))
    Filter.atTop
    (nhds (Real.exp (7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) + 1 / 4))) ∧
    Filter.Tendsto
    (fun m : ℕ =>
    ∏ n ∈ Finset.Icc 1 (2 * m),
    Real.rpow (Real.exp 1) (1 / 4) *
    (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^
    (((n * (n + 1) / 2 : ℕ) : ℤ) * (-1 : ℤ) ^ n))
    Filter.atTop
    (nhds (Real.exp (7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) - 1 / 4))) ∧
    Filter.Tendsto
    (fun m : ℕ =>
    ((∏ n ∈ Finset.Icc 1 m,
    (((2 * n : ℕ) : ℝ) ^ ((2 * n : ℕ) ^ 2))) /
    (∏ n ∈ Finset.Icc 1 m,
    (((2 * n - 1 : ℕ) : ℝ) ^ ((2 * n - 1 : ℕ) ^ 2)))) ^ 4 *
    ((((2 * m + 2 : ℕ) : ℝ) ^ (4 * m + 5)) /
    (((2 * m + 1 : ℕ) : ℝ) ^ (12 * m + 9))) ^ m)
    Filter.atTop
    (nhds (Real.exp (7 * (riemannZeta (3 : ℂ)).re / Real.pi ^ 2))) := by
-- proof
  apply MetaMathlibExt.zeta_three_infinite_product_formulas


-- created on 2026-10-20
