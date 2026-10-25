import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeObstruction.Part3
open StatMech StatMech.Ising


/--
[hasDerivAt_fourBridgeTiltMean_tanh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean)
-/
@[path]
private lemma hasDerivAt_fourBridgeTiltMean_tanh_eq
  {r a b c d : Real}
-- given
  (hP : 1 + a * Real.tanh r + b * Real.tanh r ^ 2 + c * Real.tanh r ^ 3 + d * Real.tanh r ^ 4 ≠ 0) :
-- imply
  HasDerivAt (fun u => fourBridgeTiltMean (Real.tanh u) a b c d) (fourBridgeTiltVariance (Real.tanh r) a b c d) r := by
-- proof
  apply StatMech.Ising.hasDerivAt_fourBridgeTiltMean_tanh r a b c d hP

/--
[fourBridgeVarianceSkewBernsteinCoeff_zero_eq_thirdCumulant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_zero_eq_thirdCumulant_eq
  {a b c d : Real} :
-- imply
  2 * fourBridgeVarianceSkewBernsteinCoeff a b c d 0 = (10 * a + 6 * c) - 3 * (4 + 2 * b) * a + 2 * a ^ 3 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_zero_eq_thirdCumulant a b c d

/--
[fourBridgeRankMass_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean)
-/
@[path]
private lemma fourBridgeRankMass_sum_eq
  {a b c d : Real} :
-- imply
  fourBridgeRankMass a b c d 0 + fourBridgeRankMass a b c d 1 + fourBridgeRankMass a b c d 2 + fourBridgeRankMass a b c d 3 + fourBridgeRankMass a b c d 4 = 1 := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_sum a b c d

/--
[fourBridge_endpointSix_eq_rankCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean)
-/
@[path]
private lemma fourBridge_endpointSix_eq_rankCross_eq
  {a b c d : Real} :
-- imply
  a * b + 3 * a * d - a - b * c + c * d - 3 * c = 64 * (fourBridgeRankMass a b c d 0 * fourBridgeRankMass a b c d 3 - fourBridgeRankMass a b c d 1 * fourBridgeRankMass a b c d 4) := by
-- proof
  apply StatMech.Ising.fourBridge_endpointSix_eq_rankCross a b c d

/--
[fourBridge_endpointFive_eq_rankCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean)
-/
@[path]
private lemma fourBridge_endpointFive_eq_rankCross_eq
  {a b c d : Real} :
-- imply
  2 * a * b + 3 * a * d - 3 * a - b * c - 6 * c = 32 * (fourBridgeRankMass a b c d 2 * (fourBridgeRankMass a b c d 0 - fourBridgeRankMass a b c d 4) + 3 * (fourBridgeRankMass a b c d 0 * fourBridgeRankMass a b c d 3 - fourBridgeRankMass a b c d 1 * fourBridgeRankMass a b c d 4)) := by
-- proof
  apply StatMech.Ising.fourBridge_endpointFive_eq_rankCross a b c d

/--
[fourBridge_endpointFactors_nonpos_of_rank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean)
-/
@[path]
private lemma fourBridge_endpointFactors_nonpos_of_rank_eq
  {a b c d : Real}
-- given
  (h2 : 0 <= fourBridgeRankMass a b c d 2)
  (h04 : fourBridgeRankMass a b c d 0 <= fourBridgeRankMass a b c d 4)
  (hcross : fourBridgeRankMass a b c d 0 * fourBridgeRankMass a b c d 3 <= fourBridgeRankMass a b c d 1 * fourBridgeRankMass a b c d 4) :
-- imply
  2 * a * b + 3 * a * d - 3 * a - b * c - 6 * c <= 0 ∧ a * b + 3 * a * d - a - b * c + c * d - 3 * c <= 0 := by
-- proof
  apply StatMech.Ising.fourBridge_endpointFactors_nonpos_of_rank h2 h04 hcross

/--
[fourBridgeVarianceSkewPolynomial_eq_bernstein](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewPolynomial_eq_bernstein_eq
  {t a b c d : Real} :
-- imply
  fourBridgeVarianceSkewPolynomial t a b c d = fourBridgeVarianceSkewBernsteinCoeff a b c d 0 * (1 - t ^ 2) ^ 6 + 6 * fourBridgeVarianceSkewBernsteinCoeff a b c d 1 * t ^ 2 * (1 - t ^ 2) ^ 5 + 15 * fourBridgeVarianceSkewBernsteinCoeff a b c d 2 * (t ^ 2) ^ 2 * (1 - t ^ 2) ^ 4 + 20 * fourBridgeVarianceSkewBernsteinCoeff a b c d 3 * (t ^ 2) ^ 3 * (1 - t ^ 2) ^ 3 + 15 * fourBridgeVarianceSkewBernsteinCoeff a b c d 4 * (t ^ 2) ^ 4 * (1 - t ^ 2) ^ 2 + 6 * fourBridgeVarianceSkewBernsteinCoeff a b c d 5 * (t ^ 2) ^ 5 * (1 - t ^ 2) + fourBridgeVarianceSkewBernsteinCoeff a b c d 6 * (t ^ 2) ^ 6 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewPolynomial_eq_bernstein t a b c d

/--
[fourBridgeVarianceSkewPolynomial_nonpos_of_bernstein](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewPolynomial_nonpos_of_bernstein_eq
  {t a b c d : Real}
-- given
  (ht0 : 0 <= t)
  (ht1 : t <= 1)
  (hcoeff : forall i, fourBridgeVarianceSkewBernsteinCoeff a b c d i <= 0) :
-- imply
  fourBridgeVarianceSkewPolynomial t a b c d <= 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewPolynomial_nonpos_of_bernstein ht0 ht1 hcoeff

/--
[fourBridgeTiltVariance_le_neg_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean)
-/
@[path]
private lemma fourBridgeTiltVariance_le_neg_iff_eq
  {t a b c d : Real}
-- given
  (ht0 : 0 < t)
  (ht1 : t < 1)
  (hPp : 1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4 ≠ 0)
  (hPm : 1 - a * t + b * t ^ 2 - c * t ^ 3 + d * t ^ 4 ≠ 0) :
-- imply
  fourBridgeTiltVariance t a b c d <= fourBridgeTiltVariance (-t) a b c d <-> fourBridgeVarianceSkewPolynomial t a b c d <= 0 := by
-- proof
  apply StatMech.Ising.fourBridgeTiltVariance_le_neg_iff ht0 ht1 hPp hPm


-- created on 2026-10-23
