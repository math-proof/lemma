import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.AverageOmegaHFree
open Finset ArithmeticFunction
open MeasureTheory Set intervalIntegral
open MetaMathlibExt


/--
[average_cardFactors_over_h_free](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/AverageOmegaHFree.lean)
-/
@[path]
private lemma average_cardFactors_over_h_free_eq
-- given
  (h : ℕ)
  (hh : 2 ≤ h) :
-- imply
  Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ =>
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
    (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
    (ArithmeticFunction.cardFactors n : ℝ)) -
    (1 / (riemannZeta (h : ℂ)).re) * x * Real.log (Real.log x))
    (fun x : ℝ => x) := by
-- proof
  apply MetaMathlibExt.average_cardFactors_over_h_free h hh


-- created on 2026-10-20
