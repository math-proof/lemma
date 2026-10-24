import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.LeeYangFieldAnalytic
open Finset StatMech StatMech.FrontierA


/--
[leeYangComplexFieldPartition_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldPartition_hasDerivAt_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (h : ℂ) :
-- imply
  HasDerivAt (leeYangComplexFieldPartition G beta) (leeYangComplexFieldMagnetizationNumerator G beta h) h := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldPartition_hasDerivAt beta h

/--
[leeYangComplexFieldPartition_analyticOnNhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldPartition_analyticOnNhd_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  AnalyticOnNhd ℂ (leeYangComplexFieldPartition G beta) Set.univ := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldPartition_analyticOnNhd beta

/--
[leeYangComplexFieldMagnetizationNumerator_eq_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldMagnetizationNumerator_eq_deriv_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (h : ℂ) :
-- imply
  leeYangComplexFieldMagnetizationNumerator G beta h = deriv (leeYangComplexFieldPartition G beta) h := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldMagnetizationNumerator_eq_deriv beta h

/--
[leeYangComplexFieldMagnetizationNumerator_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldMagnetizationNumerator_ofReal_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (beta h : ℝ) :
-- imply
  leeYangComplexFieldMagnetizationNumerator G beta (h : ℂ) = ((beta * ∑ s : ConfigSpace V, (∑ v : V, spin s v) * isingWeight G beta h s : ℝ) : ℂ) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldMagnetizationNumerator_ofReal beta h

/--
[leeYang_fugacity_norm_ne_one_of_re_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYang_fugacity_norm_ne_one_of_re_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {h : ℂ}
-- given
  (hbeta : 0 < beta)
  (hh : h.re ≠ 0) :
-- imply
  ‖Complex.exp (-2 * (beta : ℂ) * h)‖ ≠ 1 := by
-- proof
  apply StatMech.FrontierA.leeYang_fugacity_norm_ne_one_of_re_ne_zero hbeta hh

/--
[leeYangComplexFieldPartition_ne_zero_of_re_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldPartition_ne_zero_of_re_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {h : ℂ}
-- given
  (hbeta : 0 < beta)
  (hh : h.re ≠ 0) :
-- imply
  leeYangComplexFieldPartition G beta h ≠ 0 := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldPartition_ne_zero_of_re_ne_zero hbeta hh

/--
[leeYangComplexFieldPartition_zero_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldPartition_zero_beta_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (h : ℂ) :
-- imply
  leeYangComplexFieldPartition G 0 h = Fintype.card (ConfigSpace V) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldPartition_zero_beta h

/--
[leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {h : ℂ}
-- given
  (hbeta : 0 ≤ beta)
  (hh : h.re ≠ 0) :
-- imply
  leeYangComplexFieldPartition G beta h ≠ 0 := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero hbeta hh

/--
[leeYangComplexFieldLogDerivative_eq_logDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldLogDerivative_eq_logDeriv_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (h : ℂ) :
-- imply
  leeYangComplexFieldLogDerivative G beta h = logDeriv (leeYangComplexFieldPartition G beta) h := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldLogDerivative_eq_logDeriv beta h

/--
[leeYangComplexFieldLogDerivative_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldLogDerivative_ofReal_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (beta h : ℝ) :
-- imply
  leeYangComplexFieldLogDerivative G beta (h : ℂ) = (beta : ℂ) * (isingExpectation G beta h (fun s => ∑ v : V, spin s v) : ℂ) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldLogDerivative_ofReal beta h

/--
[leeYangComplexFieldLogDerivative_analyticOnNhd_re_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldLogDerivative_analyticOnNhd_re_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  AnalyticOnNhd ℂ (leeYangComplexFieldLogDerivative G beta) {h : ℂ | h.re ≠ 0} := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldLogDerivative_analyticOnNhd_re_ne_zero hbeta

/--
[leeYangComplexFieldLogDerivative_analyticOnNhd_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldLogDerivative_analyticOnNhd_rightHalfPlane_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  AnalyticOnNhd ℂ (leeYangComplexFieldLogDerivative G beta) {h : ℂ | 0 < h.re} := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldLogDerivative_analyticOnNhd_rightHalfPlane hbeta

/--
[leeYangComplexFieldLogDerivative_analyticOnNhd_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldLogDerivative_analyticOnNhd_leftHalfPlane_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  AnalyticOnNhd ℂ (leeYangComplexFieldLogDerivative G beta) {h : ℂ | h.re < 0} := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldLogDerivative_analyticOnNhd_leftHalfPlane hbeta

/--
[leeYangComplexFieldObservableNumerator_analyticOnNhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldObservableNumerator_analyticOnNhd_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {f : ConfigSpace V → ℂ} :
-- imply
  AnalyticOnNhd ℂ (leeYangComplexFieldObservableNumerator G beta f) Set.univ := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldObservableNumerator_analyticOnNhd beta f

/--
[leeYangComplexFieldExpectation_analyticOnNhd_re_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldExpectation_analyticOnNhd_re_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {f : ConfigSpace V → ℂ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  AnalyticOnNhd ℂ (leeYangComplexFieldExpectation G beta f) {h : ℂ | h.re ≠ 0} := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldExpectation_analyticOnNhd_re_ne_zero hbeta f

/--
[leeYangComplexFieldExpectation_analyticOnNhd_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldExpectation_analyticOnNhd_rightHalfPlane_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {f : ConfigSpace V → ℂ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  AnalyticOnNhd ℂ (leeYangComplexFieldExpectation G beta f) {h : ℂ | 0 < h.re} := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldExpectation_analyticOnNhd_rightHalfPlane hbeta f

/--
[leeYangComplexFieldExpectation_analyticOnNhd_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldExpectation_analyticOnNhd_leftHalfPlane_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {f : ConfigSpace V → ℂ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  AnalyticOnNhd ℂ (leeYangComplexFieldExpectation G beta f) {h : ℂ | h.re < 0} := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldExpectation_analyticOnNhd_leftHalfPlane hbeta f

/--
[leeYangComplexFieldObservableNumerator_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldObservableNumerator_ofReal_eq
  [Fintype V]
  [DecidableEq V]
  {f : ConfigSpace V → ℝ}
-- given
  (beta h : ℝ) :
-- imply
  leeYangComplexFieldObservableNumerator G beta (fun s => (f s : ℂ)) (h : ℂ) = ((∑ s : ConfigSpace V, f s * isingWeight G beta h s : ℝ) : ℂ) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldObservableNumerator_ofReal beta h f

/--
[leeYangComplexFieldExpectation_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean)
-/
@[path]
private lemma leeYangComplexFieldExpectation_ofReal_eq
  [Fintype V]
  [DecidableEq V]
  {f : ConfigSpace V → ℝ}
-- given
  (beta h : ℝ) :
-- imply
  leeYangComplexFieldExpectation G beta (fun s => (f s : ℂ)) (h : ℂ) = (isingExpectation G beta h f : ℂ) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldExpectation_ofReal beta h f


-- created on 2026-10-23
