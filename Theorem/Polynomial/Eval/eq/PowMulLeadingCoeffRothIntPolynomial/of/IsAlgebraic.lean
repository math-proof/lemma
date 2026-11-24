module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.NumberTheory.RothAuxiliary
public import Def.NumberTheory.RothAuxiliary.Part3
public import Def.NumberTheory.RothAuxiliary.Part7
public import Theorem.Polynomial.EvalRothPowerCoord.eq.Pow.of.EqEval_0
public import Theorem.Polynomial.Eval_AlgebraMapMulLeadingCoeffRothIntPolynomialRothIntegralPolynomial.eq.Zero.of.IsAlgebraic
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


public section

/--
[rothPowerCoord_algebraic_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private theorem main
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
-- updated on 2026-11-13
