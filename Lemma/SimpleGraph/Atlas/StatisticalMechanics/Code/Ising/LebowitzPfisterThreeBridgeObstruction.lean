import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeObstruction
open StatMech StatMech.Ising


/--
[threeBridgeVarianceSkewPolynomial_eq_bernstein](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeObstruction.lean)
-/
@[path]
private lemma threeBridgeVarianceSkewPolynomial_eq_bernstein_eq
  {t a b c : Real} :
-- imply
  threeBridgeVarianceSkewPolynomial t a b c = threeBridgeVarianceSkewBernsteinCoeff a b c 0 * (1 - t ^ 2) ^ 4 + 4 * threeBridgeVarianceSkewBernsteinCoeff a b c 1 * t ^ 2 * (1 - t ^ 2) ^ 3 + 6 * threeBridgeVarianceSkewBernsteinCoeff a b c 2 * (t ^ 2) ^ 2 * (1 - t ^ 2) ^ 2 + 4 * threeBridgeVarianceSkewBernsteinCoeff a b c 3 * (t ^ 2) ^ 3 * (1 - t ^ 2) + threeBridgeVarianceSkewBernsteinCoeff a b c 4 * (t ^ 2) ^ 4 := by
-- proof
  apply StatMech.Ising.threeBridgeVarianceSkewPolynomial_eq_bernstein t a b c

/--
[threeBridgeVarianceSkewPolynomial_nonpos_of_bernstein](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeObstruction.lean)
-/
@[path]
private lemma threeBridgeVarianceSkewPolynomial_nonpos_of_bernstein_eq
  {t a b c : Real}
-- given
  (ht0 : 0 <= t)
  (ht1 : t <= 1)
  (hcoeff : forall i, threeBridgeVarianceSkewBernsteinCoeff a b c i <= 0) :
-- imply
  threeBridgeVarianceSkewPolynomial t a b c <= 0 := by
-- proof
  apply StatMech.Ising.threeBridgeVarianceSkewPolynomial_nonpos_of_bernstein ht0 ht1 hcoeff

/--
[threeBridge_cube_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeObstruction.lean)
-/
@[path]
private lemma threeBridge_cube_inequality_eq
  {u v w : Real}
-- given
  (hu0 : 0 <= u)
  (hu1 : u <= 1)
  (hv0 : 0 <= v)
  (hv1 : v <= 1)
  (hw0 : 0 <= w)
  (hw1 : w <= 1) :
-- imply
  (u * v + u * w + v * w - 1) * (u + v + w) <= u * v * w * (u * v + u * w + v * w + 3) := by
-- proof
  apply StatMech.Ising.threeBridge_cube_inequality hu0 hu1 hv0 hv1 hw0 hw1

/--
[threeBridgeTiltVariance_le_neg_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeObstruction.lean)
-/
@[path]
private lemma threeBridgeTiltVariance_le_neg_iff_eq
  {t a b c : Real}
-- given
  (ht0 : 0 < t)
  (ht1 : t < 1)
  (hPp : 1 + a * t + b * t ^ 2 + c * t ^ 3 ≠ 0)
  (hPm : 1 - a * t + b * t ^ 2 - c * t ^ 3 ≠ 0) :
-- imply
  threeBridgeTiltVariance t a b c <= threeBridgeTiltVariance (-t) a b c <-> threeBridgeVarianceSkewPolynomial t a b c <= 0 := by
-- proof
  apply StatMech.Ising.threeBridgeTiltVariance_le_neg_iff ht0 ht1 hPp hPm

/--
[threeBridge_basicCoefficientBounds_insufficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeObstruction.lean)
-/
@[path]
private lemma threeBridge_basicCoefficientBounds_insufficient_eq :
-- imply
  let a : Real := 1 / 10 let b : Real := 1 / 10 let c : Real := 1 0 <= a ∧ a <= 1 ∧ 0 <= b ∧ b <= 1 ∧ 0 <= c ∧ c <= 1 ∧ a * a <= b ∧ b * a <= c ∧ threeBridgeTiltVariance (-1 / 2) a b c < threeBridgeTiltVariance (1 / 2) a b c := by
-- proof
  apply StatMech.Ising.threeBridge_basicCoefficientBounds_insufficient


-- created on 2026-10-23
