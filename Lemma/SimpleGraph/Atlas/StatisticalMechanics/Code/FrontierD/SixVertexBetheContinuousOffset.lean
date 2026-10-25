import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffset.Part2
open StatMech StatMech.FrontierD


/--
[sixVertexContinuousOffsetKernel_eq_thetaRightDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffset.lean)
-/
@[path]
private lemma sixVertexContinuousOffsetKernel_eq_thetaRightDerivative_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexContinuousOffsetKernel c x y = deriv (fun t => sixVertexTheta c x t) y := by
-- proof
  apply StatMech.FrontierD.sixVertexContinuousOffsetKernel_eq_thetaRightDerivative hc x y

/--
[continuous_sixVertexContinuousOffsetSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffset.lean)
-/
@[path]
private lemma continuous_sixVertexContinuousOffsetSource_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Continuous (sixVertexContinuousOffsetSource c) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexContinuousOffsetSource hc

/--
[odd_sixVertexContinuousOffsetSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffset.lean)
-/
@[path]
private lemma odd_sixVertexContinuousOffsetSource_eq
  {c : Real} :
-- imply
  Function.Odd (sixVertexContinuousOffsetSource c) := by
-- proof
  apply StatMech.FrontierD.odd_sixVertexContinuousOffsetSource c

/--
[sixVertexRootDensityWeight_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffset.lean)
-/
@[path]
private lemma sixVertexRootDensityWeight_neg_eq
  {c x : Real} :
-- imply
  sixVertexRootDensityWeight c (-x) = sixVertexRootDensityWeight c x := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityWeight_neg c x

/--
[intervalIntegral_neg_pi_pi_eq_zero_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffset.lean)
-/
@[path]
private lemma intervalIntegral_neg_pi_pi_eq_zero_of_odd_eq
  {f : Real → Real}
-- given
  (hf : Function.Odd f) :
-- imply
  (∫ x in -Real.pi..Real.pi, f x) = 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_neg_pi_pi_eq_zero_of_odd hf

/--
[sixVertexContinuousOffsetEquation_unique_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffset.lean)
-/
@[path]
private lemma sixVertexContinuousOffsetEquation_unique_of_odd_eq
  {c : Real}
  {tau sigma : Real → Real}
-- given
  (hc : 2 < c)
  (htau : Continuous tau)
  (hsigma : Continuous sigma)
  (htauOdd : Function.Odd tau)
  (hsigmaOdd : Function.Odd sigma)
  (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
  (hsigmaEq : SixVertexSatisfiesContinuousOffsetEquation c sigma) :
-- imply
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi, tau x = sigma x := by
-- proof
  apply StatMech.FrontierD.sixVertexContinuousOffsetEquation_unique_of_odd hc htau hsigma htauOdd hsigmaOdd htauEq hsigmaEq


-- created on 2026-10-23
