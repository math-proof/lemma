import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangLogDerivativeBound.Part2
open Polynomial StatMech StatMech.FrontierA


/--
[leeYangFugacityLogDerivative_norm_le_openUnitDisk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLogDerivativeBound.lean)
-/
@[path]
private lemma leeYangFugacityLogDerivative_norm_le_openUnitDisk_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℂ}
-- given
  (hbeta : 0 ≤ beta)
  (hz : ‖z‖ < 1) :
-- imply
  ‖leeYangFugacityLogDerivative G beta z‖ ≤ (Fintype.card V : ℝ) / (1 - ‖z‖) := by
-- proof
  apply StatMech.FrontierA.leeYangFugacityLogDerivative_norm_le_openUnitDisk hbeta hz

/--
[leeYangFugacityLogDerivative_norm_le_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLogDerivativeBound.lean)
-/
@[path]
private lemma leeYangFugacityLogDerivative_norm_le_exterior_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℂ}
-- given
  (hbeta : 0 ≤ beta)
  (hz : 1 < ‖z‖) :
-- imply
  ‖leeYangFugacityLogDerivative G beta z‖ ≤ (Fintype.card V : ℝ) / (‖z‖ - 1) := by
-- proof
  apply StatMech.FrontierA.leeYangFugacityLogDerivative_norm_le_exterior hbeta hz

/--
[leeYangComplexFieldLogDerivative_eq_fugacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLogDerivativeBound.lean)
-/
@[path]
private lemma leeYangComplexFieldLogDerivative_eq_fugacity_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {h : ℂ}
-- given
  (hbeta : 0 ≤ beta)
  (hh : h.re ≠ 0) :
-- imply
  leeYangComplexFieldLogDerivative G beta h = (beta : ℂ) * Fintype.card V - 2 * (beta : ℂ) * Complex.exp (-2 * (beta : ℂ) * h) * leeYangFugacityLogDerivative G beta (Complex.exp (-2 * (beta : ℂ) * h)) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldLogDerivative_eq_fugacity hbeta hh

/--
[leeYangComplexFieldLogDerivative_norm_le_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLogDerivativeBound.lean)
-/
@[path]
private lemma leeYangComplexFieldLogDerivative_norm_le_rightHalfPlane_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {h : ℂ}
-- given
  (hbeta : 0 < beta)
  (hh : 0 < h.re) :
-- imply
  ‖leeYangComplexFieldLogDerivative G beta h‖ ≤ (Fintype.card V : ℝ) * (beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ / (1 - ‖Complex.exp (-2 * (beta : ℂ) * h)‖)) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldLogDerivative_norm_le_rightHalfPlane hbeta hh

/--
[leeYangComplexFieldLogDerivative_norm_le_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLogDerivativeBound.lean)
-/
@[path]
private lemma leeYangComplexFieldLogDerivative_norm_le_leftHalfPlane_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {h : ℂ}
-- given
  (hbeta : 0 < beta)
  (hh : h.re < 0) :
-- imply
  ‖leeYangComplexFieldLogDerivative G beta h‖ ≤ (Fintype.card V : ℝ) * (beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ / (‖Complex.exp (-2 * (beta : ℂ) * h)‖ - 1)) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldLogDerivative_norm_le_leftHalfPlane hbeta hh

/--
[leeYangNormalizedFieldLogDerivative_analyticOnNhd_re_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLogDerivativeBound.lean)
-/
@[path]
private lemma leeYangNormalizedFieldLogDerivative_analyticOnNhd_re_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  AnalyticOnNhd ℂ (leeYangNormalizedFieldLogDerivative G beta) {h : ℂ | h.re ≠ 0} := by
-- proof
  apply StatMech.FrontierA.leeYangNormalizedFieldLogDerivative_analyticOnNhd_re_ne_zero hbeta

/--
[leeYangNormalizedFieldLogDerivative_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLogDerivativeBound.lean)
-/
@[path]
private lemma leeYangNormalizedFieldLogDerivative_ofReal_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (beta h : ℝ) :
-- imply
  leeYangNormalizedFieldLogDerivative G beta (h : ℂ) = (beta : ℂ) * (isingExpectation G beta h (fun s => ∑ v : V, spin s v) : ℂ) / Fintype.card V := by
-- proof
  apply StatMech.FrontierA.leeYangNormalizedFieldLogDerivative_ofReal beta h

/--
[leeYangNormalizedFieldLogDerivative_norm_le_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLogDerivativeBound.lean)
-/
@[path]
private lemma leeYangNormalizedFieldLogDerivative_norm_le_rightHalfPlane_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {beta : ℝ}
  {h : ℂ}
-- given
  (hbeta : 0 < beta)
  (hh : 0 < h.re) :
-- imply
  ‖leeYangNormalizedFieldLogDerivative G beta h‖ ≤ beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ / (1 - ‖Complex.exp (-2 * (beta : ℂ) * h)‖) := by
-- proof
  apply StatMech.FrontierA.leeYangNormalizedFieldLogDerivative_norm_le_rightHalfPlane hbeta hh

/--
[leeYangNormalizedFieldLogDerivative_norm_le_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLogDerivativeBound.lean)
-/
@[path]
private lemma leeYangNormalizedFieldLogDerivative_norm_le_leftHalfPlane_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {beta : ℝ}
  {h : ℂ}
-- given
  (hbeta : 0 < beta)
  (hh : h.re < 0) :
-- imply
  ‖leeYangNormalizedFieldLogDerivative G beta h‖ ≤ beta + 2 * beta * ‖Complex.exp (-2 * (beta : ℂ) * h)‖ / (‖Complex.exp (-2 * (beta : ℂ) * h)‖ - 1) := by
-- proof
  apply StatMech.FrontierA.leeYangNormalizedFieldLogDerivative_norm_le_leftHalfPlane hbeta hh


-- created on 2026-10-23
