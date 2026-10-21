import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.Eval.eq.MulMulProd_ChoosePowLeadingCoeffRothIntPolynomialSumPow_RothTermDegree.of.RothBox.IsAlgebraic
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothAuxCombination_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ)
  {m : ℕ}
  {r : Fin m → ℕ}
-- given
  (hα : IsAlgebraic ℚ α)
  (i : RothBox r)
  (c : RothCoeff r) :
-- imply
  eval₂ (algebraMap ℤ ℝ)
    (((rothIntPolynomial α).leadingCoeff : ℝ) * α)
    (rothAuxCombination α i c) =
    ((rothIntPolynomial α).leadingCoeff : ℝ) ^ (∑ h, r h) *
      rothHasseEval c (fun h ↦ i h) (fun _ ↦ α) := by
-- proof
  rw [rothAuxCombination, eval₂_finsetSum]
  unfold rothHasseEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [eval₂_mul, eval₂_C,
    Eval.eq.MulMulProd_ChoosePowLeadingCoeffRothIntPolynomialSumPow_RothTermDegree.of.RothBox.IsAlgebraic
      α hα i j]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [algebraMap_int_eq, Int.coe_castRingHom]
  dsimp only
  simp only [rothTermDegree]
  ring


-- created on 2026-10-21
