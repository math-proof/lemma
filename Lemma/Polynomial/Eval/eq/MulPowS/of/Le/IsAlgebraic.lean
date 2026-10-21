import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.Eval.eq.PowMulLeadingCoeffRothIntPolynomial.of.IsAlgebraic
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothScaledPowerCoord_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ)
  {S n : ℕ}
-- given
  (hn : n ≤ S)
  (hα : IsAlgebraic ℚ α) :
-- imply
  eval₂ (algebraMap ℤ ℝ)
    (((rothIntPolynomial α).leadingCoeff : ℝ) * α)
    (rothScaledPowerCoord α S n) =
    ((rothIntPolynomial α).leadingCoeff : ℝ) ^ S * α ^ n := by
-- proof
  let a := (rothIntPolynomial α).leadingCoeff
  rw [rothScaledPowerCoord, eval₂_mul, eval₂_C,
    Eval.eq.PowMulLeadingCoeffRothIntPolynomial.of.IsAlgebraic α n hα]
  change ((a ^ (S - n) : ℤ) : ℝ) * (((a : ℝ) * α) ^ n) = _
  push_cast
  rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]


-- created on 2026-10-21
