/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeCounting/SquarefreeTotientWeighted.lean -/


import sympy.atlas.NumberTheory.PrimeCounting.SquarefreeTotientWeighted
import Lemma.Nat.PrimeCounting.SquarefreeTotientWeighted
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.NumberTheory.PrimeCounting.SquarefreeTotientWeighted

open scoped BigOperators

open MathlibExt.NumberTheory.PrimeCounting

-- Specialize the weighted squarefree-totient lower bound at its endpoint.
example :
    Real.log 100 + 36 / 100 <
      ∑ q ∈ Finset.Icc 1 (100 : ℕ), (1 + (q : ℝ) / 100)⁻¹ *
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / Nat.totient q) := by
  exact squarefreeTotientWeightedLower 100 (by norm_num)

end MathlibExtTest.NumberTheory.PrimeCounting.SquarefreeTotientWeighted
