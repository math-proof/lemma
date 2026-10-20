import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.GandhiNthPrimeFormula
open scoped BigOperators
open MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormulaWanted


/--
[gandhi_nthPrimeFormula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/GandhiNthPrimeFormula.lean)
-/
@[path]
private lemma gandhi_nthPrimeFormula_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  ((Nat.nth Nat.Prime (n - 1) : ℕ) : ℤ) =
    ⌊1 - Real.logb 2 (-1 / 2 +
    ∑ d ∈ Nat.divisors
    (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)),
    (((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1)))⌋ := by
-- proof
  apply MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormulaWanted.gandhi_nthPrimeFormula n hn


-- created on 2026-10-20
