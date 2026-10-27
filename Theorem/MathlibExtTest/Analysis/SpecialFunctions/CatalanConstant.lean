/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/CatalanConstant.lean -/


import Theorem.Analysis.SpecialFunctions.CatalanConstant


example : Real.catalanConstant =
    ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 :=
  Real.catalanConstant_eq_tsum

example : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2)
    Real.catalanConstant :=
  Real.hasSum_catalanConstant

#print axioms Real.catalanConstant

