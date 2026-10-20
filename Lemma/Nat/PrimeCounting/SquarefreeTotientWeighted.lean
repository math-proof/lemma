import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.SquarefreeTotientWeighted
open scoped BigOperators
open Finset MeasureTheory
open MathlibExt.NumberTheory.PrimeCounting


/--
[squarefreeTotientWeightedLower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/SquarefreeTotientWeighted.lean)
-/
@[path]
private lemma squarefreeTotientWeightedLower_eq
  {z : ℕ}
-- given
  (hz : 100 ≤ z) :
-- imply
  Real.log z + 36 / 100 <
    ∑ q ∈ Finset.Icc 1 z, (1 + (q : ℝ) / z)⁻¹ *
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / Nat.totient q) := by
-- proof
  apply MathlibExt.NumberTheory.PrimeCounting.squarefreeTotientWeightedLower z hz


-- created on 2026-10-20
