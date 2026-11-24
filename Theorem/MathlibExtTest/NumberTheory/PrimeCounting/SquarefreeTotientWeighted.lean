module
public import Def.NumberTheory.PrimeCounting.SquarefreeTotientWeighted
public import Theorem.Nat.PrimeCounting.SquarefreeTotientWeighted
public import Mathlib.Tactic.NormNum


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeCounting/SquarefreeTotientWeighted.lean -/
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
