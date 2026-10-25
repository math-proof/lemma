import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierC.IsingTransfer.Part5
open Matrix Polynomial StatMech StatMech.FrontierC


/--
[isingTransfer_disc_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_disc_sq_eq
-- given
  (beta h : ℝ) :
-- imply
  isingTransferDisc beta h ^ 2 = (transferA beta h - transferD beta h) ^ 2 + 4 * transferB beta ^ 2 := by
-- proof
  apply StatMech.FrontierC.isingTransfer_disc_sq beta h

/--
[isingTransfer_eigen_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_eigen_sum_eq
-- given
  (beta h : ℝ) :
-- imply
  isingTransferEigenPlus beta h + isingTransferEigenMinus beta h = transferA beta h + transferD beta h := by
-- proof
  apply StatMech.FrontierC.isingTransfer_eigen_sum beta h

/--
[isingTransfer_eigen_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_eigen_prod_eq
-- given
  (beta h : ℝ) :
-- imply
  isingTransferEigenPlus beta h * isingTransferEigenMinus beta h = transferA beta h * transferD beta h - transferB beta ^ 2 := by
-- proof
  apply StatMech.FrontierC.isingTransfer_eigen_prod beta h

/--
[isingTransfer_disc_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_disc_pos_eq
-- given
  (beta h : ℝ) :
-- imply
  0 < isingTransferDisc beta h := by
-- proof
  apply StatMech.FrontierC.isingTransfer_disc_pos beta h

/--
[isingTransfer_eigenPlus_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_eigenPlus_pos_eq
-- given
  (beta h : ℝ) :
-- imply
  0 < isingTransferEigenPlus beta h := by
-- proof
  apply StatMech.FrontierC.isingTransfer_eigenPlus_pos beta h

/--
[isingTransfer_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_trace_eq
-- given
  (beta h : ℝ) :
-- imply
  (isingTransfer beta h).trace = ((transferA beta h + transferD beta h : ℝ) : ℂ) := by
-- proof
  apply StatMech.FrontierC.isingTransfer_trace beta h

/--
[isingTransfer_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_det_eq
-- given
  (beta h : ℝ) :
-- imply
  (isingTransfer beta h).det = ((transferA beta h * transferD beta h - transferB beta ^ 2 : ℝ) : ℂ) := by
-- proof
  apply StatMech.FrontierC.isingTransfer_det beta h

/--
[isingTransfer_charpoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_charpoly_eq
-- given
  (beta h : ℝ) :
-- imply
  (isingTransfer beta h).charpoly = (X - C (isingTransferEigenPlus beta h : ℂ)) * (X - C (isingTransferEigenMinus beta h : ℂ)) := by
-- proof
  apply StatMech.FrontierC.isingTransfer_charpoly beta h

/--
[isingTransfer_roots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_roots_eq
-- given
  (beta h : ℝ) :
-- imply
  (isingTransfer beta h).charpoly.roots = {(isingTransferEigenPlus beta h : ℂ), (isingTransferEigenMinus beta h : ℂ)} := by
-- proof
  apply StatMech.FrontierC.isingTransfer_roots beta h

/--
[isingTransfer_trace_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_trace_pow_eq
  {n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  ((isingTransfer beta h) ^ n).trace = (isingTransferEigenPlus beta h : ℂ) ^ n + (isingTransferEigenMinus beta h : ℂ) ^ n := by
-- proof
  apply StatMech.FrontierC.isingTransfer_trace_pow beta h n

/--
[transferSpin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma transferSpin_zero_eq :
-- imply
  transferSpin 0 = 1 := by
-- proof
  apply StatMech.FrontierC.transferSpin_zero

/--
[transferSpin_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma transferSpin_one_eq :
-- imply
  transferSpin 1 = -1 := by
-- proof
  apply StatMech.FrontierC.transferSpin_one

/--
[isingTransfer_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_apply_eq
  {s t : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  isingTransfer beta h s t = (Real.exp (beta * transferSpin s * transferSpin t + (h / 2) * (transferSpin s + transferSpin t)) : ℂ) := by
-- proof
  apply StatMech.FrontierC.isingTransfer_apply beta h s t

/--
[sum_transferSpin_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma sum_transferSpin_add_one_eq
  {n : ℕ}
  [NeZero n]
  {s : Fin n → Fin 2} :
-- imply
  (∑ k : Fin n, transferSpin (s (k + 1))) = ∑ k : Fin n, transferSpin (s k) := by
-- proof
  apply StatMech.FrontierC.sum_transferSpin_add_one s

/--
[isingTransfer_loopWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_loopWeight_eq
  {n : ℕ}
  [NeZero n]
  {s : Fin n → Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  (∏ k : Fin n, isingTransfer beta h (s k) (s (k + 1))) = (Real.exp (isingRingExponent beta h s) : ℂ) := by
-- proof
  apply StatMech.FrontierC.isingTransfer_loopWeight beta h s

/--
[isingRingZ_eq_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingRingZ_eq_trace_eq
  {n : ℕ}
  [NeZero n]
-- given
  (hn : 0 < n)
  (beta h : ℝ) :
-- imply
  (isingRingZ n beta h : ℂ) = ((isingTransfer beta h) ^ n).trace := by
-- proof
  apply StatMech.FrontierC.isingRingZ_eq_trace n hn beta h

/--
[isingRingZ_eigenvalues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingRingZ_eigenvalues_eq
  {n : ℕ}
  [NeZero n]
-- given
  (hn : 0 < n)
  (beta h : ℝ) :
-- imply
  (isingRingZ n beta h : ℂ) = (isingTransferEigenPlus beta h : ℂ) ^ n + (isingTransferEigenMinus beta h : ℂ) ^ n := by
-- proof
  apply StatMech.FrontierC.isingRingZ_eigenvalues n hn beta h

/--
[isingRingZ_eigenvalues_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingRingZ_eigenvalues_real_eq
  {n : ℕ}
  [NeZero n]
-- given
  (hn : 0 < n)
  (beta h : ℝ) :
-- imply
  isingRingZ n beta h = isingTransferEigenPlus beta h ^ n + isingTransferEigenMinus beta h ^ n := by
-- proof
  apply StatMech.FrontierC.isingRingZ_eigenvalues_real n hn beta h

/--
[isingRingZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingRingZ_pos_eq
  {n : ℕ}
  [NeZero n]
-- given
  (beta h : ℝ) :
-- imply
  0 < isingRingZ n beta h := by
-- proof
  apply StatMech.FrontierC.isingRingZ_pos n beta h

/--
[isingTransfer_abs_eigenMinus_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_abs_eigenMinus_lt_eq
-- given
  (beta h : ℝ) :
-- imply
  |isingTransferEigenMinus beta h| < isingTransferEigenPlus beta h := by
-- proof
  apply StatMech.FrontierC.isingTransfer_abs_eigenMinus_lt beta h

/--
[isingTransfer_eigenRatio_abs_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_eigenRatio_abs_lt_one_eq
-- given
  (beta h : ℝ) :
-- imply
  |isingTransferEigenMinus beta h / isingTransferEigenPlus beta h| < 1 := by
-- proof
  apply StatMech.FrontierC.isingTransfer_eigenRatio_abs_lt_one beta h

/--
[isingRing_pressure_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingRing_pressure_tendsto_eq
-- given
  (beta h : ℝ) :
-- imply
  Filter.Tendsto (fun n : ℕ => Real.log (isingRingZ (n + 1) beta h) / (n + 1 : ℝ)) Filter.atTop (nhds (Real.log (isingTransferEigenPlus beta h))) := by
-- proof
  apply StatMech.FrontierC.isingRing_pressure_tendsto beta h

/--
[isingTransferEigenPlus_closed_form](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransferEigenPlus_closed_form_eq
-- given
  (beta h : ℝ) :
-- imply
  isingTransferEigenPlus beta h = Real.exp beta * Real.cosh h + Real.sqrt (Real.exp (2 * beta) * Real.sinh h ^ 2 + Real.exp (-2 * beta)) := by
-- proof
  apply StatMech.FrontierC.isingTransferEigenPlus_closed_form beta h

/--
[isingRing_pressure_closed_form](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingRing_pressure_closed_form_eq
-- given
  (beta h : ℝ) :
-- imply
  Filter.Tendsto (fun n : ℕ => Real.log (isingRingZ (n + 1) beta h) / (n + 1 : ℝ)) Filter.atTop (nhds (Real.log (Real.exp beta * Real.cosh h + Real.sqrt (Real.exp (2 * beta) * Real.sinh h ^ 2 + Real.exp (-2 * beta))))) := by
-- proof
  apply StatMech.FrontierC.isingRing_pressure_closed_form beta h

/--
[isingPressureClosedForm_analyticAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingPressureClosedForm_analyticAt_eq
  {x : ℝ × ℝ} :
-- imply
  AnalyticAt ℝ isingPressureClosedForm x := by
-- proof
  apply StatMech.FrontierC.isingPressureClosedForm_analyticAt x

/--
[isingTransfer_eigenMinus_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransfer_eigenMinus_nonneg_eq
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (h : ℝ) :
-- imply
  0 ≤ isingTransferEigenMinus beta h := by
-- proof
  apply StatMech.FrontierC.isingTransfer_eigenMinus_nonneg hbeta h

/--
[isingTransferCorrelationRatio_mem_Ico](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransferCorrelationRatio_mem_Ico_eq
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (h : ℝ) :
-- imply
  isingTransferCorrelationRatio beta h ∈ Set.Ico 0 1 := by
-- proof
  apply StatMech.FrontierC.isingTransferCorrelationRatio_mem_Ico hbeta h

/--
[isingTransferCorrelationRatio_pow_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean)
-/
@[path]
private lemma isingTransferCorrelationRatio_pow_tendsto_zero_eq
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (h : ℝ) :
-- imply
  Filter.Tendsto (fun n : ℕ => isingTransferCorrelationRatio beta h ^ n) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierC.isingTransferCorrelationRatio_pow_tendsto_zero hbeta h


-- created on 2026-10-23
