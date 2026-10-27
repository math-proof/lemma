import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.CatalanConstantProducts.Part7


/--
[CatalanConstantProducts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/CatalanConstantProducts.lean)
-/
@[path]
private lemma catalan_constant_product_formulas_is
-- given
  (G : ℝ)
  (hG : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2) G) :
-- imply
  (Filter.Tendsto (fun m : ℕ => ∏ n ∈ Finset.Icc 1 (2 * m),
      (1 - 2 / (2 * (n : ℝ) + 1)) ^ ((n : ℤ) * (-1 : ℤ) ^ n))
    Filter.atTop (nhds (Real.exp (2 * G / Real.pi - 1 / 2)))) ∧
  (Filter.Tendsto (fun m : ℕ => ∏ n ∈ Finset.Icc 1 (2 * m + 1),
      (1 - 2 / (2 * (n : ℝ) + 1)) ^ ((n : ℤ) * (-1 : ℤ) ^ n))
    Filter.atTop (nhds (Real.exp (2 * G / Real.pi + 1 / 2)))) ∧
  Filter.Tendsto (fun m : ℕ =>
      ((∏ k ∈ Finset.range m, (4 * (k : ℝ) + 3) ^ (4 * k + 3)) /
        (∏ k ∈ Finset.range m, (4 * (k : ℝ) + 1) ^ (4 * k + 1))) ^ 2 *
      (4 * (m : ℝ) + 3) ^ (2 * m + 1) / (4 * (m : ℝ) + 1) ^ (6 * m + 1))
    Filter.atTop (nhds (Real.exp (4 * G / Real.pi))) := by
-- proof
  apply MetaMathlibExt.catalan_constant_product_formulas G hG


-- created on 2026-10-11
