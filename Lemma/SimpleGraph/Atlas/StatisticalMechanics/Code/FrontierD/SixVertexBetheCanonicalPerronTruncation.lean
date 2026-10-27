import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexBetheLogNumerator_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexBetheLogNumerator_lower_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  (c ^ 2 - 2) ^ 2 <= sixVertexBetheLogNumerator c x := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheLogNumerator_lower hc x

/--
[sixVertexBetheLogNumerator_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexBetheLogNumerator_pos_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexBetheLogNumerator c x := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheLogNumerator_pos hc x

/--
[sixVertexBetheLogDenominator_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexBetheLogDenominator_nonneg_eq
  {x : Real} :
-- imply
  0 <= sixVertexBetheLogDenominator x := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheLogDenominator_nonneg x

/--
[abs_sixVertexBetheLogNumerator_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma abs_sixVertexBetheLogNumerator_sub_le_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  |sixVertexBetheLogNumerator c x - sixVertexBetheLogNumerator c y| <= (2 * (c ^ 2 - 1)) * |x - y| := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBetheLogNumerator_sub_le hc x y

/--
[abs_sixVertexBetheLogDenominator_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma abs_sixVertexBetheLogDenominator_sub_le_eq
  {x y : Real} :
-- imply
  |sixVertexBetheLogDenominator x - sixVertexBetheLogDenominator y| <= 2 * |x - y| := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBetheLogDenominator_sub_le x y

/--
[lipschitzWith_sixVertexRegularizedBetheLogKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexRegularizedBetheLogKernel_eq
  {c epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  LipschitzWith (sixVertexRegularizedBetheLogLipschitzConstant c epsilon) (sixVertexRegularizedBetheLogKernel c epsilon) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexRegularizedBetheLogKernel hc hepsilon

/--
[exists_lipschitzWith_sixVertexRegularizedBetheLogKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma exists_lipschitzWith_sixVertexRegularizedBetheLogKernel_eq
  {c epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ C : NNReal, LipschitzWith C (sixVertexRegularizedBetheLogKernel c epsilon) := by
-- proof
  apply StatMech.FrontierD.exists_lipschitzWith_sixVertexRegularizedBetheLogKernel hc hepsilon

/--
[continuous_sixVertexRegularizedBetheLogKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma continuous_sixVertexRegularizedBetheLogKernel_eq
  {c epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Continuous (sixVertexRegularizedBetheLogKernel c epsilon) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexRegularizedBetheLogKernel hc hepsilon

/--
[periodic_sixVertexRegularizedBetheLogKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma periodic_sixVertexRegularizedBetheLogKernel_eq
  {c epsilon : Real} :
-- imply
  Function.Periodic (sixVertexRegularizedBetheLogKernel c epsilon) (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.periodic_sixVertexRegularizedBetheLogKernel c epsilon

/--
[even_sixVertexRegularizedBetheLogKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma even_sixVertexRegularizedBetheLogKernel_eq
  {c epsilon : Real} :
-- imply
  Function.Even (sixVertexRegularizedBetheLogKernel c epsilon) := by
-- proof
  apply StatMech.FrontierD.even_sixVertexRegularizedBetheLogKernel c epsilon

/--
[sixVertexCanonicalDensityPerronEmpiricalRegularized_eq_positiveHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronEmpiricalRegularized_eq_positiveHalf_eq
  {c : Real}
  {epsilon : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexRegularizedBetheLogKernel c epsilon) k = (2 * ∑ j : Fin (k + 1), sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j)) / (sixVertexFourWidth 0 k : Real) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronEmpiricalRegularized_eq_positiveHalf hc epsilon k

/--
[sixVertexBetheM_log_norm_eq_logNumerator_sub_logDenominator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexBetheM_log_norm_eq_logNumerator_sub_logDenominator_eq
  {c p : Real}
-- given
  (hc : 2 < c)
  (hp : sixVertexBethePhase p ≠ 1) :
-- imply
  Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ = (1 / 2 : Real) * (Real.log (sixVertexBetheLogNumerator c p) - Real.log (sixVertexBetheLogDenominator p)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheM_log_norm_eq_logNumerator_sub_logDenominator hc hp

/--
[sixVertexRegularizedBetheLogKernel_error_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexRegularizedBetheLogKernel_error_bounds_eq
  {c p epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hp : sixVertexBethePhase p ≠ 1) :
-- imply
  0 <= Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ - sixVertexRegularizedBetheLogKernel c epsilon p ∧ Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ - sixVertexRegularizedBetheLogKernel c epsilon p <= epsilon / (2 * sixVertexBetheLogDenominator p) := by
-- proof
  apply StatMech.FrontierD.sixVertexRegularizedBetheLogKernel_error_bounds hc hepsilon hp

/--
[sixVertexRegularizedBetheLogKernel_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexRegularizedBetheLogKernel_nonneg_eq
  {c epsilon : Real}
  {p : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hepsilonUpper : epsilon <= (c ^ 2 - 2) ^ 2 - 4) :
-- imply
  0 <= sixVertexRegularizedBetheLogKernel c epsilon p := by
-- proof
  apply StatMech.FrontierD.sixVertexRegularizedBetheLogKernel_nonneg hc hepsilon hepsilonUpper p

/--
[sixVertexCanonicalDensityPerronLogDenominator_quantile_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronLogDenominator_quantile_lower_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  4 * (2 * (j : Real) + 1) ^ 2 <= (sixVertexFourWidth 0 k : Real) ^ 2 * sixVertexBetheLogDenominator (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronLogDenominator_quantile_lower hc k j

/--
[sum_Ico_inv_odd_sq_le_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sum_Ico_inv_odd_sq_le_inv_eq
  {J K : Nat}
-- given
  (hJ : 0 < J) :
-- imply
  (∑ j ∈ Finset.Ico J K, (1 : Real) / (2 * (j : Real) + 1) ^ 2) <= 1 / (J : Real) := by
-- proof
  apply StatMech.FrontierD.sum_Ico_inv_odd_sq_le_inv J K hJ

/--
[sixVertexCanonicalDensityPerronRootAverage_sub_regularized_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronRootAverage_sub_regularized_eq_eq
  {c : Real}
  {epsilon : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k - sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexRegularizedBetheLogKernel c epsilon) k = (2 * ∑ j : Fin (k + 1), (Real.log ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ - sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))) / (sixVertexFourWidth 0 k : Real) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronRootAverage_sub_regularized_eq hc epsilon k

/--
[sixVertexCanonicalDensityPerronRegularized_pointwise_error_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronRegularized_pointwise_error_le_eq
  {c epsilon : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Real.log ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ - sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j) <= epsilon * (sixVertexFourWidth 0 k : Real) ^ 2 / (8 * (2 * (j : Real) + 1) ^ 2) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronRegularized_pointwise_error_le hc hepsilon k j

/--
[sixVertexCanonicalDensityPerronRegularized_tail_error_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronRegularized_tail_error_le_eq
  {c epsilon : Real}
  {J : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hJ : 0 < J) :
-- imply
  (2 * ∑ j : Fin (k + 1) with J <= j.val, (Real.log ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ - sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))) / (sixVertexFourWidth 0 k : Real) <= epsilon * (sixVertexFourWidth 0 k : Real) / (4 * (J : Real)) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronRegularized_tail_error_le hc hepsilon hJ k

/--
[sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds_eq
  {c epsilon : Real}
  {J : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hepsilonUpper : epsilon <= (c ^ 2 - 2) ^ 2 - 4)
  (hJ : 0 < J) :
-- imply
  0 <= sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k - sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexRegularizedBetheLogKernel c epsilon) k ∧ sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k - sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexRegularizedBetheLogKernel c epsilon) k <= sixVertexCanonicalDensityPerronInitialLogContribution hc J k + epsilon * (sixVertexFourWidth 0 k : Real) / (4 * (J : Real)) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds hc hepsilon hepsilonUpper hJ k

/--
[sixVertexCanonicalLinearEdgeCutoff_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexCanonicalLinearEdgeCutoff_pos_eq
  {eta : Real}
  {k : Nat}
-- given
  (heta : 0 < eta) :
-- imply
  0 < sixVertexCanonicalLinearEdgeCutoff eta k := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalLinearEdgeCutoff_pos heta k

/--
[sixVertexCanonicalLinearEdgeCutoff_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexCanonicalLinearEdgeCutoff_le_eq
  {eta : Real}
  {k : Nat}
-- given
  (heta : eta <= 1 / 4) :
-- imply
  sixVertexCanonicalLinearEdgeCutoff eta k <= k + 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalLinearEdgeCutoff_le heta k

/--
[tendsto_sixVertexCanonicalLinearEdgeCutoff_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalLinearEdgeCutoff_ratio_eq
  {eta : Real}
-- given
  (heta : 0 <= eta) :
-- imply
  Tendsto (fun k : Nat => (sixVertexCanonicalLinearEdgeCutoff eta k : Real) / (sixVertexFourWidth 0 k : Real)) atTop (nhds eta) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalLinearEdgeCutoff_ratio heta

/--
[tendsto_sixVertexCanonicalRegularizationUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalRegularizationUpper_eq
  {c epsilon eta : Real}
-- given
  (hc0 : c ≠ 0)
  (heta : 0 < eta) :
-- imply
  Tendsto (sixVertexCanonicalRegularizationUpper c epsilon eta) atTop (nhds (sixVertexCanonicalRegularizationEnvelope c epsilon eta)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalRegularizationUpper hc0 heta

/--
[sixVertexCanonicalDensityPerronRootAverage_regularized_error_le_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronRootAverage_regularized_error_le_upper_eq
  {c epsilon eta : Real}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hepsilonUpper : epsilon <= (c ^ 2 - 2) ^ 2 - 4)
  (heta : 0 < eta)
  (hetaUpper : eta <= 1 / 4) :
-- imply
  sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k - sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexRegularizedBetheLogKernel c epsilon) k <= sixVertexCanonicalRegularizationUpper c epsilon eta k := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronRootAverage_regularized_error_le_upper hc hepsilon hepsilonUpper heta hetaUpper k

/--
[tendsto_sixVertexCanonicalRegularizationDiagonalEnvelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalRegularizationDiagonalEnvelope_eq
  {c : Real}
-- given
  (hc0 : c ≠ 0) :
-- imply
  Tendsto (sixVertexCanonicalRegularizationDiagonalEnvelope c) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalRegularizationDiagonalEnvelope hc0

/--
[eventually_exists_sixVertexCanonicalRegularizedApproximation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma eventually_exists_sixVertexCanonicalRegularizedApproximation_eq
  {c : Real}
  {delta : Real}
-- given
  (hc : 2 < c)
  (hdelta : 0 < delta) :
-- imply
  ∃ eta : Real, 0 < eta ∧ eta <= 1 / 4 ∧ eta ^ 2 <= (c ^ 2 - 2) ^ 2 - 4 ∧ ∀ᶠ k : Nat in atTop, sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k - sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexRegularizedBetheLogKernel c (eta ^ 2)) k < delta := by
-- proof
  apply StatMech.FrontierD.eventually_exists_sixVertexCanonicalRegularizedApproximation hc hdelta

/--
[tendsto_sixVertexCanonicalDensityPerronRegularizedLogKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalDensityPerronRegularizedLogKernel_eq
  {c epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Tendsto (sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexRegularizedBetheLogKernel c epsilon)) atTop (nhds (∫ y in -Real.pi..Real.pi, sixVertexRegularizedBetheLogKernel c epsilon y * sixVertexFourierPhysicalDensity c hc y)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalDensityPerronRegularizedLogKernel hc hepsilon

/--
[cauchySeq_sixVertexCanonicalDensityPerronRootAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma cauchySeq_sixVertexCanonicalDensityPerronRootAverage_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  CauchySeq (sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc)) := by
-- proof
  apply StatMech.FrontierD.cauchySeq_sixVertexCanonicalDensityPerronRootAverage hc

/--
[exists_sixVertexCanonicalDensityPerronRootAverage_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma exists_sixVertexCanonicalDensityPerronRootAverage_limit_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∃ a : Real, Tendsto (sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc)) atTop (nhds a) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexCanonicalDensityPerronRootAverage_limit hc

/--
[tendsto_sixVertexCanonicalDensityPerronRootAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalDensityPerronRootAverage_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc)) atTop (nhds (sixVertexCanonicalDensityPerronRootAverageLimit hc)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalDensityPerronRootAverage hc

/--
[abs_sixVertexCanonicalDensityPerronRootAverageLimit_sub_regularizedIntegral_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalDensityPerronRootAverageLimit_sub_regularizedIntegral_le_eq
  {c eta : Real}
-- given
  (hc : 2 < c)
  (heta : 0 < eta)
  (hetaQuarter : eta <= 1 / 4)
  (hetaSq : eta ^ 2 <= (c ^ 2 - 2) ^ 2 - 4) :
-- imply
  |sixVertexCanonicalDensityPerronRootAverageLimit hc - ∫ y in -Real.pi..Real.pi, sixVertexRegularizedBetheLogKernel c (eta ^ 2) y * sixVertexFourierPhysicalDensity c hc y| <= sixVertexCanonicalRegularizationDiagonalEnvelope c eta := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalDensityPerronRootAverageLimit_sub_regularizedIntegral_le hc heta hetaQuarter hetaSq

/--
[tendsto_sixVertexCentralWidthRate_canonicalDensityPerronLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean)
-/
@[path]
private lemma tendsto_sixVertexCentralWidthRate_canonicalDensityPerronLimit_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCentralWidthRate c) atTop (nhds (sixVertexCanonicalDensityPerronRootAverageLimit hc)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCentralWidthRate_canonicalDensityPerronLimit hc


-- created on 2026-10-23
