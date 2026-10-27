import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.LogNonnegativeSinusoid
open MeasureTheory Polynomial StatMech StatMech.FrontierA


/--
[nonnegativeSinusoidQ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LogNonnegativeSinusoid.lean)
-/
@[path]
private lemma nonnegativeSinusoidQ_pos_eq
  {A u v : Real}
-- given
  (hA : 0 < A)
  (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2)) :
-- imply
  0 < nonnegativeSinusoidQ A u v := by
-- proof
  apply StatMech.FrontierA.nonnegativeSinusoidQ_pos hA hdisc

/--
[nonnegativeSinusoidRoot_norm_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LogNonnegativeSinusoid.lean)
-/
@[path]
private lemma nonnegativeSinusoidRoot_norm_le_one_eq
  {A u v : Real}
-- given
  (hA : 0 < A)
  (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2)) :
-- imply
  ‖nonnegativeSinusoidRoot A u v‖ ≤ 1 := by
-- proof
  apply StatMech.FrontierA.nonnegativeSinusoidRoot_norm_le_one hA hdisc

/--
[nonnegativeSinusoidPolynomial_logMahler](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LogNonnegativeSinusoid.lean)
-/
@[path]
private lemma nonnegativeSinusoidPolynomial_logMahler_eq
  {A u v : Real}
-- given
  (hA : 0 < A)
  (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2)) :
-- imply
  (nonnegativeSinusoidPolynomial A u v).logMahlerMeasure = Real.log (nonnegativeSinusoidQ A u v / 2) := by
-- proof
  apply StatMech.FrontierA.nonnegativeSinusoidPolynomial_logMahler hA hdisc

/--
[norm_eval_nonnegativeSinusoidPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LogNonnegativeSinusoid.lean)
-/
@[path]
private lemma norm_eval_nonnegativeSinusoidPolynomial_eq
  {A u v : Real}
  {z : Complex}
-- given
  (hA : 0 < A)
  (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2))
  (hz : ‖z‖ = 1) :
-- imply
  ‖eval z (nonnegativeSinusoidPolynomial A u v)‖ = A - u * z.re - v * z.im := by
-- proof
  apply StatMech.FrontierA.norm_eval_nonnegativeSinusoidPolynomial hA hdisc hz

/--
[circleAverage_log_nonnegativeSinusoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LogNonnegativeSinusoid.lean)
-/
@[path]
private lemma circleAverage_log_nonnegativeSinusoid_eq
  {A u v : Real}
-- given
  (hA : 0 < A)
  (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2)) :
-- imply
  Real.circleAverage (fun z : Complex => Real.log (A - u * z.re - v * z.im)) 0 1 = Real.log (nonnegativeSinusoidQ A u v / 2) := by
-- proof
  apply StatMech.FrontierA.circleAverage_log_nonnegativeSinusoid hA hdisc

/--
[integral_log_nonnegativeSinusoid_zero_two_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LogNonnegativeSinusoid.lean)
-/
@[path]
private lemma integral_log_nonnegativeSinusoid_zero_two_pi_eq
  {A u v : Real}
-- given
  (hA : 0 < A)
  (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2)) :
-- imply
  (∫ theta in (0 : Real)..(2 * Real.pi), Real.log (A - u * Real.cos theta - v * Real.sin theta)) = 2 * Real.pi * Real.log (nonnegativeSinusoidQ A u v / 2) := by
-- proof
  apply StatMech.FrontierA.integral_log_nonnegativeSinusoid_zero_two_pi hA hdisc

/--
[integral_log_nonnegativeSinusoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LogNonnegativeSinusoid.lean)
-/
@[path]
private lemma integral_log_nonnegativeSinusoid_eq
  {A u v : Real}
-- given
  (hA : 0 < A)
  (hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2)) :
-- imply
  (∫ theta in (-Real.pi)..Real.pi, Real.log (A - u * Real.cos theta - v * Real.sin theta)) = 2 * Real.pi * Real.log (nonnegativeSinusoidQ A u v / 2) := by
-- proof
  apply StatMech.FrontierA.integral_log_nonnegativeSinusoid hA hdisc


-- created on 2026-10-23
