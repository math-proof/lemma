import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.LeeYangZeroFree
open Finset Polynomial StatMech StatMech.FrontierA


/--
[leeYangComplexFieldPartition_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangZeroFree.lean)
-/
@[path]
private lemma leeYangComplexFieldPartition_ofReal_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (beta h : ℝ) :
-- imply
  leeYangComplexFieldPartition G beta (h : ℂ) = (isingZ G beta h : ℂ) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldPartition_ofReal beta h

/--
[leeYangComplexFieldPartition_eq_fugacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangZeroFree.lean)
-/
@[path]
private lemma leeYangComplexFieldPartition_eq_fugacity_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (h : ℂ) :
-- imply
  (leeYangComplexPolynomial G beta).eval (Complex.exp (-2 * (beta : ℂ) * h)) = Complex.exp (-(beta : ℂ) * h * Fintype.card V) * leeYangComplexFieldPartition G beta h := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldPartition_eq_fugacity beta h

/--
[leeYangComplexPolynomial_ne_zero_of_norm_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangZeroFree.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_ne_zero_of_norm_ne_one_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℂ}
-- given
  (hbeta : 0 ≤ beta)
  (hz : ‖z‖ ≠ 1) :
-- imply
  (leeYangComplexPolynomial G beta).eval z ≠ 0 := by
-- proof
  apply StatMech.FrontierA.leeYangComplexPolynomial_ne_zero_of_norm_ne_one hbeta hz

/--
[leeYangComplexFieldPartition_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangZeroFree.lean)
-/
@[path]
private lemma leeYangComplexFieldPartition_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {h : ℂ}
-- given
  (hbeta : 0 ≤ beta)
  (hfugacity : ‖Complex.exp (-2 * (beta : ℂ) * h)‖ ≠ 1) :
-- imply
  leeYangComplexFieldPartition G beta h ≠ 0 := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldPartition_ne_zero hbeta hfugacity

/--
[leeYangFugacityLogDerivative_eq_logDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangZeroFree.lean)
-/
@[path]
private lemma leeYangFugacityLogDerivative_eq_logDeriv_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℂ} :
-- imply
  leeYangFugacityLogDerivative G beta z = logDeriv (fun w ↦ (leeYangComplexPolynomial G beta).eval w) z := by
-- proof
  apply StatMech.FrontierA.leeYangFugacityLogDerivative_eq_logDeriv beta z

/--
[leeYangFugacityLogDerivative_analyticOnNhd_offCircle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangZeroFree.lean)
-/
@[path]
private lemma leeYangFugacityLogDerivative_analyticOnNhd_offCircle_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  AnalyticOnNhd ℂ (leeYangFugacityLogDerivative G beta) {z : ℂ | ‖z‖ ≠ 1} := by
-- proof
  apply StatMech.FrontierA.leeYangFugacityLogDerivative_analyticOnNhd_offCircle hbeta

/--
[leeYangFugacityLogDerivative_analyticOnNhd_openUnitDisk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangZeroFree.lean)
-/
@[path]
private lemma leeYangFugacityLogDerivative_analyticOnNhd_openUnitDisk_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  AnalyticOnNhd ℂ (leeYangFugacityLogDerivative G beta) {z : ℂ | ‖z‖ < 1} := by
-- proof
  apply StatMech.FrontierA.leeYangFugacityLogDerivative_analyticOnNhd_openUnitDisk hbeta

/--
[leeYangFugacityLogDerivative_analyticOnNhd_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangZeroFree.lean)
-/
@[path]
private lemma leeYangFugacityLogDerivative_analyticOnNhd_exterior_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  AnalyticOnNhd ℂ (leeYangFugacityLogDerivative G beta) {z : ℂ | 1 < ‖z‖} := by
-- proof
  apply StatMech.FrontierA.leeYangFugacityLogDerivative_analyticOnNhd_exterior hbeta


-- created on 2026-10-23
