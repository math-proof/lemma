import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocals
open MathlibExt.SelbergSieve
open MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted


/--
[brun_twin_prime_reciprocal_series_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brun_twin_prime_reciprocal_series_summable_eq
  :
-- imply
  Summable (fun p : ℕ =>
    if p.Prime ∧ (p + 2).Prime then
    (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p + 2 : ℕ) : ℝ)
    else 0) := by
-- proof
  apply MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted.brun_twin_prime_reciprocal_series_summable


-- created on 2026-10-20
