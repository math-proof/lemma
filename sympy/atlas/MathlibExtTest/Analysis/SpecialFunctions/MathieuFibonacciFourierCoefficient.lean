/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/MathieuFibonacciFourierCoefficient.lean -/


import sympy.atlas.Analysis.SpecialFunctions.MathieuFibonacciFourierCoefficient

namespace MetaMathlibExt

example (n : {n : ℕ // 1 ≤ n}) :
    mathieuFibonacciFourierCoefficient n =
      (2 / Real.log ((1 + Real.sqrt 5) / 2)) *
        ‖Complex.Gamma (1 + 2 * (n.val : ℂ) * (Real.pi : ℂ) * Complex.I /
          (Real.log ((1 + Real.sqrt 5) / 2) : ℂ))‖ ^ 2 :=
  rfl

end MetaMathlibExt
