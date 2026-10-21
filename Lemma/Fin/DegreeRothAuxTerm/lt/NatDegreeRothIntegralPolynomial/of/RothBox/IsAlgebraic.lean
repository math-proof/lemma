import Mathlib
import Lemma.Polynomial.DegreeRothPowerCoord.lt.NatDegree.of.GtNatDegree_0.Monic
import Lemma.Rat.MonicRothIntegralPolynomial.of.IsAlgebraic
import Lemma.Rat.NatDegreeRothIntegralPolynomial.Gt_0.of.IsAlgebraic
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial Rat


/--
[rothAuxTerm_degree_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ)
-- given
  (hα : IsAlgebraic ℚ α)
  {m : ℕ}
  {r : Fin m → ℕ}
  (i j : RothBox r) :
-- imply
  (rothAuxTerm α i j).degree < (rothIntegralPolynomial α).natDegree := by
-- proof
  have degree_C_mul_lt {P : ℤ[X]} {d : ℕ} (hP : P.degree < d) (c : ℤ) :
    (C c * P).degree < d := by
    if hc : c = 0 then
      simp [hc]
    else
      rwa [degree_C_mul hc]
  unfold rothAuxTerm rothScaledPowerCoord
  apply degree_C_mul_lt
  apply degree_C_mul_lt
  exact DegreeRothPowerCoord.lt.NatDegree.of.GtNatDegree_0.Monic
    (rothIntegralPolynomial α) (rothTermDegree i j)
    (NatDegreeRothIntegralPolynomial.Gt_0.of.IsAlgebraic hα)
    (MonicRothIntegralPolynomial.of.IsAlgebraic hα)


-- created on 2026-10-21
