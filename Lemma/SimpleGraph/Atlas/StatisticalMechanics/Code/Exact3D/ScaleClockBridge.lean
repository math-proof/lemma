import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.ScaleClockBridge
open StatMech StatMech.Exact3D


/--
[tendsto_scaleClock_ratio_of_eventually_annulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_scaleClock_ratio_of_eventually_annulus_eq
  {M : CriticalModel ι}
  {clock : ℝ → ℝ}
  {relevantEigenvalue cLo cHi : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hcLo : 0 < cLo)
  (_hcHi : 0 < cHi)
  (hannulus : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ∧ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ≤ cHi) :
-- imply
  Filter.Tendsto (fun β : ℝ => clock β / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds ((Real.log relevantEigenvalue)⁻¹)) := by
-- proof
  apply StatMech.Exact3D.tendsto_scaleClock_ratio_of_eventually_annulus M clock relevantEigenvalue cLo cHi heigen hcLo _hcHi hannulus

/--
[criticalDistanceScaleClock_annulus_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma criticalDistanceScaleClock_annulus_eq_eq
  {M : CriticalModel ι}
  {relevantEigenvalue β : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hβ : 0 < M.betaC - β) :
-- imply
  Real.exp (criticalDistanceScaleClock M relevantEigenvalue β * Real.log relevantEigenvalue) * (M.betaC - β) = 1 := by
-- proof
  apply StatMech.Exact3D.criticalDistanceScaleClock_annulus_eq M heigen hβ

/--
[criticalDistanceScaleClock_annulus_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma criticalDistanceScaleClock_annulus_eventually_eq
  {M : CriticalModel ι}
  {relevantEigenvalue : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue) :
-- imply
  ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), (1 : ℝ) ≤ Real.exp (criticalDistanceScaleClock M relevantEigenvalue β * Real.log relevantEigenvalue) * (M.betaC - β) ∧ Real.exp (criticalDistanceScaleClock M relevantEigenvalue β * Real.log relevantEigenvalue) * (M.betaC - β) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.criticalDistanceScaleClock_annulus_eventually M heigen

/--
[tendsto_criticalDistanceScaleClock_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_criticalDistanceScaleClock_ratio_eq
  {M : CriticalModel ι}
  {relevantEigenvalue : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue) :
-- imply
  Filter.Tendsto (fun β : ℝ => criticalDistanceScaleClock M relevantEigenvalue β / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds ((Real.log relevantEigenvalue)⁻¹)) := by
-- proof
  apply StatMech.Exact3D.tendsto_criticalDistanceScaleClock_ratio M heigen

/--
[tendsto_sublinear_criticalDistanceScaleClock_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_sublinear_criticalDistanceScaleClock_self_eq
  {M : CriticalModel ι}
  {relevantEigenvalue : ℝ} :
-- imply
  Filter.Tendsto (fun β : ℝ => (criticalDistanceScaleClock M relevantEigenvalue β - criticalDistanceScaleClock M relevantEigenvalue β) / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_sublinear_criticalDistanceScaleClock_self M relevantEigenvalue

/--
[tendsto_scaleClock_ratio_of_sublinear_criticalDistanceScaleClock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_scaleClock_ratio_of_sublinear_criticalDistanceScaleClock_eq
  {M : CriticalModel ι}
  {clock : ℝ → ℝ}
  {relevantEigenvalue : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hcompare : Filter.Tendsto (fun β : ℝ => (clock β - criticalDistanceScaleClock M relevantEigenvalue β) / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  Filter.Tendsto (fun β : ℝ => clock β / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds ((Real.log relevantEigenvalue)⁻¹)) := by
-- proof
  apply StatMech.Exact3D.tendsto_scaleClock_ratio_of_sublinear_criticalDistanceScaleClock M clock heigen hcompare

/--
[tendsto_sublinear_criticalDistanceScaleClock_of_scaleClock_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_sublinear_criticalDistanceScaleClock_of_scaleClock_ratio_eq
  {M : CriticalModel ι}
  {clock : ℝ → ℝ}
  {relevantEigenvalue : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hclock : Filter.Tendsto (fun β : ℝ => clock β / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds ((Real.log relevantEigenvalue)⁻¹))) :
-- imply
  Filter.Tendsto (fun β : ℝ => (clock β - criticalDistanceScaleClock M relevantEigenvalue β) / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_sublinear_criticalDistanceScaleClock_of_scaleClock_ratio M clock heigen hclock

/--
[tendsto_scaleClock_ratio_iff_sublinear_criticalDistanceScaleClock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_scaleClock_ratio_iff_sublinear_criticalDistanceScaleClock_eq
  {M : CriticalModel ι}
  {clock : ℝ → ℝ}
  {relevantEigenvalue : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue) :
-- imply
  Filter.Tendsto (fun β : ℝ => clock β / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds ((Real.log relevantEigenvalue)⁻¹)) ↔ Filter.Tendsto (fun β : ℝ => (clock β - criticalDistanceScaleClock M relevantEigenvalue β) / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_scaleClock_ratio_iff_sublinear_criticalDistanceScaleClock M clock heigen

/--
[tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus_eq
  {M : CriticalModel ι}
  {clock : ℝ → ℝ}
  {relevantEigenvalue cLo cHi : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hannulus : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ∧ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ≤ cHi) :
-- imply
  Filter.Tendsto (fun β : ℝ => (clock β - criticalDistanceScaleClock M relevantEigenvalue β) / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus M clock relevantEigenvalue cLo cHi heigen hcLo hcHi hannulus

/--
[eventually_pos_of_sublinear_criticalDistanceScaleClock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma eventually_pos_of_sublinear_criticalDistanceScaleClock_eq
  {M : CriticalModel ι}
  {clock : ℝ → ℝ}
  {relevantEigenvalue : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hcompare : Filter.Tendsto (fun β : ℝ => (clock β - criticalDistanceScaleClock M relevantEigenvalue β) / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < clock β := by
-- proof
  apply StatMech.Exact3D.eventually_pos_of_sublinear_criticalDistanceScaleClock M clock heigen hcompare

/--
[tendsto_terminal_add_error_div_log_betaC_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_terminal_add_error_div_log_betaC_sub_eq
  {M : CriticalModel ι}
  {terminalLog accumulatedError : ℝ → ℝ}
  {terminalLimit : ℝ}
-- given
  (hterminal : Filter.Tendsto terminalLog (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds terminalLimit))
  (herror : Filter.Tendsto (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  Filter.Tendsto (fun β : ℝ => (terminalLog β + accumulatedError β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_terminal_add_error_div_log_betaC_sub M terminalLog accumulatedError terminalLimit hterminal herror

/--
[eventually_abs_le_abs_limit_add_one_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma eventually_abs_le_abs_limit_add_one_of_tendsto_eq
  {l : Filter α}
  {f : α → ℝ}
  {a : ℝ}
-- given
  (hf : Filter.Tendsto f l (nhds a)) :
-- imply
  ∀ᶠ x in l, := by
-- proof
  apply StatMech.Exact3D.eventually_abs_le_abs_limit_add_one_of_tendsto hf

/--
[tendsto_bounded_terminal_add_error_div_log_betaC_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_bounded_terminal_add_error_div_log_betaC_sub_eq
  {M : CriticalModel ι}
  {terminalLog accumulatedError : ℝ → ℝ}
  {terminalBound : ℝ}
-- given
  (hterminal : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), |terminalLog β| ≤ terminalBound)
  (herror : Filter.Tendsto (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  Filter.Tendsto (fun β : ℝ => (terminalLog β + accumulatedError β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_bounded_terminal_add_error_div_log_betaC_sub M terminalLog accumulatedError terminalBound hterminal herror

/--
[tendsto_error_div_neg_log_betaC_sub_iff_log_betaC_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_error_div_neg_log_betaC_sub_iff_log_betaC_sub_eq
  {M : CriticalModel ι}
  {accumulatedError : ℝ → ℝ} :
-- imply
  Filter.Tendsto (fun β : ℝ => accumulatedError β / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) ↔ Filter.Tendsto (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_error_div_neg_log_betaC_sub_iff_log_betaC_sub M accumulatedError

/--
[tendsto_error_div_clock_of_log_betaC_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_error_div_clock_of_log_betaC_sub_eq
  {M : CriticalModel ι}
  {clock accumulatedError : ℝ → ℝ}
  {relevantEigenvalue : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hclock_compare : Filter.Tendsto (fun β : ℝ => (clock β - criticalDistanceScaleClock M relevantEigenvalue β) / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (herror : Filter.Tendsto (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  Filter.Tendsto (fun β : ℝ => accumulatedError β / clock β) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_error_div_clock_of_log_betaC_sub M clock accumulatedError heigen hclock_compare herror

/--
[tendsto_error_div_clock_of_log_betaC_sub_of_annulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_error_div_clock_of_log_betaC_sub_of_annulus_eq
  {M : CriticalModel ι}
  {clock accumulatedError : ℝ → ℝ}
  {relevantEigenvalue cLo cHi : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hannulus : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ∧ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ≤ cHi)
  (herror : Filter.Tendsto (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  Filter.Tendsto (fun β : ℝ => accumulatedError β / clock β) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_error_div_clock_of_log_betaC_sub_of_annulus M clock accumulatedError relevantEigenvalue cLo cHi heigen hcLo hcHi hannulus herror

/--
[tendsto_error_div_log_betaC_sub_of_clock_average](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_error_div_log_betaC_sub_of_clock_average_eq
  {M : CriticalModel ι}
  {clock accumulatedError : ℝ → ℝ}
  {relevantEigenvalue : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hclock_compare : Filter.Tendsto (fun β : ℝ => (clock β - criticalDistanceScaleClock M relevantEigenvalue β) / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (haverage : Filter.Tendsto (fun β : ℝ => accumulatedError β / clock β) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  Filter.Tendsto (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_error_div_log_betaC_sub_of_clock_average M clock accumulatedError heigen hclock_compare haverage

/--
[tendsto_error_div_log_betaC_sub_of_annulus_clock_average](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_error_div_log_betaC_sub_of_annulus_clock_average_eq
  {M : CriticalModel ι}
  {clock accumulatedError : ℝ → ℝ}
  {relevantEigenvalue cLo cHi : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hannulus : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ∧ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ≤ cHi)
  (haverage : Filter.Tendsto (fun β : ℝ => accumulatedError β / clock β) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  Filter.Tendsto (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_error_div_log_betaC_sub_of_annulus_clock_average M clock accumulatedError relevantEigenvalue cLo cHi heigen hcLo hcHi hannulus haverage

/--
[tendsto_error_div_clock_iff_log_betaC_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_error_div_clock_iff_log_betaC_sub_eq
  {M : CriticalModel ι}
  {clock accumulatedError : ℝ → ℝ}
  {relevantEigenvalue : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hclock_compare : Filter.Tendsto (fun β : ℝ => (clock β - criticalDistanceScaleClock M relevantEigenvalue β) / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  Filter.Tendsto (fun β : ℝ => accumulatedError β / clock β) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) ↔ Filter.Tendsto (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_error_div_clock_iff_log_betaC_sub M clock accumulatedError heigen hclock_compare

/--
[tendsto_error_div_clock_iff_log_betaC_sub_of_annulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_error_div_clock_iff_log_betaC_sub_of_annulus_eq
  {M : CriticalModel ι}
  {clock accumulatedError : ℝ → ℝ}
  {relevantEigenvalue cLo cHi : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hannulus : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ∧ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ≤ cHi) :
-- imply
  Filter.Tendsto (fun β : ℝ => accumulatedError β / clock β) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) ↔ Filter.Tendsto (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_error_div_clock_iff_log_betaC_sub_of_annulus M clock accumulatedError relevantEigenvalue cLo cHi heigen hcLo hcHi hannulus

/--
[tendsto_bounded_terminal_add_error_div_log_betaC_sub_of_clock_average](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_bounded_terminal_add_error_div_log_betaC_sub_of_clock_average_eq
  {M : CriticalModel ι}
  {clock terminalLog accumulatedError : ℝ → ℝ}
  {terminalBound : ℝ}
  {relevantEigenvalue : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hclock_compare : Filter.Tendsto (fun β : ℝ => (clock β - criticalDistanceScaleClock M relevantEigenvalue β) / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hterminal : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), |terminalLog β| ≤ terminalBound)
  (haverage : Filter.Tendsto (fun β : ℝ => accumulatedError β / clock β) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  Filter.Tendsto (fun β : ℝ => (terminalLog β + accumulatedError β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_bounded_terminal_add_error_div_log_betaC_sub_of_clock_average M clock terminalLog accumulatedError terminalBound heigen hclock_compare hterminal haverage

/--
[tendsto_bounded_terminal_add_error_div_log_betaC_sub_of_annulus_clock_average](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_bounded_terminal_add_error_div_log_betaC_sub_of_annulus_clock_average_eq
  {M : CriticalModel ι}
  {clock terminalLog accumulatedError : ℝ → ℝ}
  {terminalBound : ℝ}
  {relevantEigenvalue cLo cHi : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hannulus : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ∧ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ≤ cHi)
  (hterminal : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), |terminalLog β| ≤ terminalBound)
  (haverage : Filter.Tendsto (fun β : ℝ => accumulatedError β / clock β) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  Filter.Tendsto (fun β : ℝ => (terminalLog β + accumulatedError β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_bounded_terminal_add_error_div_log_betaC_sub_of_annulus_clock_average M clock terminalLog accumulatedError terminalBound relevantEigenvalue cLo cHi heigen hcLo hcHi hannulus hterminal haverage

/--
[tendsto_terminal_add_error_div_log_betaC_sub_of_clock_average](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_terminal_add_error_div_log_betaC_sub_of_clock_average_eq
  {M : CriticalModel ι}
  {clock terminalLog accumulatedError : ℝ → ℝ}
  {terminalLimit : ℝ}
  {relevantEigenvalue : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hclock_compare : Filter.Tendsto (fun β : ℝ => (clock β - criticalDistanceScaleClock M relevantEigenvalue β) / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hterminal : Filter.Tendsto terminalLog (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds terminalLimit))
  (haverage : Filter.Tendsto (fun β : ℝ => accumulatedError β / clock β) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  Filter.Tendsto (fun β : ℝ => (terminalLog β + accumulatedError β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_terminal_add_error_div_log_betaC_sub_of_clock_average M clock terminalLog accumulatedError terminalLimit heigen hclock_compare hterminal haverage

/--
[tendsto_terminal_add_error_div_log_betaC_sub_of_annulus_clock_average](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_terminal_add_error_div_log_betaC_sub_of_annulus_clock_average_eq
  {M : CriticalModel ι}
  {clock terminalLog accumulatedError : ℝ → ℝ}
  {terminalLimit : ℝ}
  {relevantEigenvalue cLo cHi : ℝ}
-- given
  (heigen : 1 < relevantEigenvalue)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hannulus : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ∧ Real.exp (clock β * Real.log relevantEigenvalue) * (M.betaC - β) ≤ cHi)
  (hterminal : Filter.Tendsto terminalLog (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds terminalLimit))
  (haverage : Filter.Tendsto (fun β : ℝ => accumulatedError β / clock β) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  Filter.Tendsto (fun β : ℝ => (terminalLog β + accumulatedError β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_terminal_add_error_div_log_betaC_sub_of_annulus_clock_average M clock terminalLog accumulatedError terminalLimit relevantEigenvalue cLo cHi heigen hcLo hcHi hannulus hterminal haverage

/--
[tendsto_log_mass_div_log_betaC_sub_of_scaleClock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean)
-/
@[path]
private lemma tendsto_log_mass_div_log_betaC_sub_of_scaleClock_eq
  {M : CriticalModel ι}
  {mass clock logError : ℝ → ℝ}
  {scaleBase relevantEigenvalue : ℝ}
-- given
  (hclock : Filter.Tendsto (fun β : ℝ => clock β / (-Real.log (M.betaC - β))) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds ((Real.log relevantEigenvalue)⁻¹)))
  (herror : Filter.Tendsto (fun β : ℝ => logError β / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hlog : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), Real.log (mass β) = -(Real.log scaleBase) * clock β + logError β) :
-- imply
  Filter.Tendsto (fun β : ℝ => Real.log (mass β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds (Real.log scaleBase / Real.log relevantEigenvalue)) := by
-- proof
  apply StatMech.Exact3D.tendsto_log_mass_div_log_betaC_sub_of_scaleClock M mass clock logError scaleBase relevantEigenvalue hclock herror hlog


-- created on 2026-10-23
