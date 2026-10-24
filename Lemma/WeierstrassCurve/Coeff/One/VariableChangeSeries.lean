import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_WeierstrassCurve_VariableChangeSeries
import Lemma.Int.P2MUtil
open Int


/--
[WeierstrassCurve_coeff_one_variableChangeSeries](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_coeff_one_variableChangeSeries.lean)
-/
@[path]
private lemma main
  [CommRing R]
  {W : WeierstrassCurve R}
  {C : WeierstrassCurve.VariableChange R} :
-- imply
  PowerSeries.coeff 1 (W.variableChangeSeries C) = (C.u : R) := by
-- proof
  unfold WeierstrassCurve.variableChangeSeries
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (PowerSeries.C (C.u : R) * (PowerSeries.X - PowerSeries.C C.r * W.formalW)) *
      PowerSeries.coeff j ((W.variableChangeDenom C).invOfUnit 1)) 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply ((W.variableChangeDenom C).invOfUnit 1),
    PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one, mul_one]
  simp [PowerSeries.coeff_C_mul, W.constantCoeff_formalW, W.coeff_formalW_one, PowerSeries.coeff_X]


-- created on 2026-10-24
