import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.EvalRothPowerCoord.eq.Pow.of.EqEval_0
import Lemma.Polynomial.Eval_AlgebraMapMulLeadingCoeffRothIntPolynomialRothIntegralPolynomial.eq.Zero.of.IsAlgebraic
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPowerCoord_algebraic_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ)
  (n : ℕ)
-- given
  (hα : IsAlgebraic ℚ α) :
-- imply
  eval₂ (algebraMap ℤ ℝ)
    (((rothIntPolynomial α).leadingCoeff : ℝ) * α)
    (rothPowerCoord (rothIntegralPolynomial α) n) =
    (((rothIntPolynomial α).leadingCoeff : ℝ) * α) ^ n := by
-- proof
  apply EvalRothPowerCoord.eq.Pow.of.EqEval_0
  exact Eval_AlgebraMapMulLeadingCoeffRothIntPolynomialRothIntegralPolynomial.eq.Zero.of.IsAlgebraic α hα


-- created on 2026-10-21
