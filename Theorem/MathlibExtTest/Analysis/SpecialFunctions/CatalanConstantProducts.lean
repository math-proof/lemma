/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/CatalanConstantProducts.lean -/


import Theorem.Analysis.SpecialFunctions.CatalanConstantProducts.Part7
open scoped BigOperators


-- The first conjunct gives the even-product limit for the supplied Catalan series.
example (G : ℝ)
    (hG : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((2 * (n : ℝ) + 1) ^ 2)) G) :
    Filter.Tendsto (fun m : ℕ => ∏ n ∈ Finset.Icc 1 (2 * m),
      (1 - 2 / (2 * (n : ℝ) + 1)) ^ ((n : ℤ) * (-1 : ℤ) ^ n))
      Filter.atTop (nhds (Real.exp (2 * G / Real.pi - 1 / 2))) := by
  exact (MetaMathlibExt.catalan_constant_product_formulas G hG).1

