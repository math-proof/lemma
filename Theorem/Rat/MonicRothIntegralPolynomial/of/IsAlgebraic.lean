module
public import Mathlib
public import Theorem.Rat.RothIntPolynomial.ne.Zero.of.IsAlgebraic
open MathlibExt.NumberTheory.RothAuxiliary
open Rat
open scoped Polynomial


public section

/--
[rothIntegralPolynomial_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private theorem main
  {α : ℝ}
-- given
  (hα : IsAlgebraic ℚ α) :
-- imply
  (rothIntegralPolynomial α).Monic := by
-- proof
  apply Polynomial.monic_integralNormalization
    (RothIntPolynomial.ne.Zero.of.IsAlgebraic hα)


-- created on 2026-10-21
