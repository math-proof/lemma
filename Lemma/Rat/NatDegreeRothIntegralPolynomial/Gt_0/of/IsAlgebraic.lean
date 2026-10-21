import Mathlib
import Lemma.Rat.NatDegreeRothIntPolynomial.Gt_0.of.IsAlgebraic
open MathlibExt.NumberTheory.RothAuxiliary
open Rat
open scoped Polynomial


/--
[rothIntegralPolynomial_natDegree_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {α : ℝ}
-- given
  (hα : IsAlgebraic ℚ α) :
-- imply
  0 < (rothIntegralPolynomial α).natDegree := by
-- proof
  simpa [rothIntegralPolynomial] using
    NatDegreeRothIntPolynomial.Gt_0.of.IsAlgebraic hα


-- created on 2026-10-21
