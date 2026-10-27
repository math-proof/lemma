import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianTrivialityReduction.Part2
open Filter Finset Topology StatMech StatMech.FrontierA


/--
[renormalizedFourPointCoupling_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTrivialityReduction.lean)
-/
@[path]
private lemma renormalizedFourPointCoupling_tendsto_zero_eq
  {fourthMoment variance normalization : ℕ → ℝ}
  {normalizationLimit : ℝ}
-- given
  (hfourthCumulant : Tendsto (fun n => scalarFourthCumulant (fourthMoment n) (variance n)) atTop (nhds 0))
  (hnormalization : Tendsto normalization atTop (nhds normalizationLimit))
  (hnormalizationLimit : normalizationLimit ≠ 0) :
-- imply
  Tendsto (fun n => renormalizedFourPointCoupling (fourthMoment n) (variance n) (normalization n)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.renormalizedFourPointCoupling_tendsto_zero fourthMoment variance normalization normalizationLimit hfourthCumulant hnormalization hnormalizationLimit

/--
[scalarMomentCumulantRecurrence_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTrivialityReduction.lean)
-/
@[path]
private lemma scalarMomentCumulantRecurrence_limit_eq
  {moments cumulants : ℕ → ℕ → ℝ}
  {limitMoments : ℕ → ℝ}
  {variance : ℝ}
-- given
  (hrecurrence : HasScalarMomentCumulantRecurrence moments cumulants)
  (hmoments : ∀ order, Tendsto (fun scale => moments scale order) atTop (nhds (limitMoments order)))
  (hcumulants : ∀ order, Tendsto (fun scale => cumulants scale order) atTop (nhds (scalarGaussianCumulant variance order))) :
-- imply
  ∀ order, limitMoments (order + 1) = ∑ k ∈ Finset.range (order + 1), (order.choose k : ℝ) * scalarGaussianCumulant variance (k + 1) * limitMoments (order - k) := by
-- proof
  apply StatMech.FrontierA.scalarMomentCumulantRecurrence_limit moments cumulants limitMoments variance hrecurrence hmoments hcumulants

/--
[scalarWickMoments_of_cumulant_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTrivialityReduction.lean)
-/
@[path]
private lemma scalarWickMoments_of_cumulant_limits_eq
  {moments cumulants : ℕ → ℕ → ℝ}
  {limitMoments : ℕ → ℝ}
  {variance : ℝ}
-- given
  (hrecurrence : HasScalarMomentCumulantRecurrence moments cumulants)
  (hmoments : ∀ order, Tendsto (fun scale => moments scale order) atTop (nhds (limitMoments order)))
  (hcumulants : ∀ order, Tendsto (fun scale => cumulants scale order) atTop (nhds (scalarGaussianCumulant variance order))) :
-- imply
  ScalarWickMoments variance limitMoments := by
-- proof
  apply StatMech.FrontierA.scalarWickMoments_of_cumulant_limits moments cumulants limitMoments variance hrecurrence hmoments hcumulants

/--
[ScalarWickMoments.odd_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTrivialityReduction.lean)
-/
@[path]
private lemma odd_eq_zero_eq
  {variance : ℝ}
  {moments : ℕ → ℝ}
-- given
  (hwick : ScalarWickMoments variance moments) :
-- imply
  ∀ n, moments (2 * n + 1) = 0 := by
-- proof
  apply StatMech.FrontierA.ScalarWickMoments.odd_eq_zero hwick

/--
[ScalarWickMoments.fourth_eq_three_mul_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTrivialityReduction.lean)
-/
@[path]
private lemma fourth_eq_three_mul_sq_eq
  {variance : ℝ}
  {moments : ℕ → ℝ}
-- given
  (hwick : ScalarWickMoments variance moments) :
-- imply
  moments 4 = 3 * variance ^ 2 := by
-- proof
  apply StatMech.FrontierA.ScalarWickMoments.fourth_eq_three_mul_sq hwick


-- created on 2026-10-23
