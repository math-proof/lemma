import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWeightedQuadrature
open MeasureTheory StatMech StatMech.FrontierD


/--
[abs_left_mul_densityIntegral_sub_integral_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWeightedQuadrature.lean)
-/
@[path]
private lemma abs_left_mul_densityIntegral_sub_integral_mul_le_eq :
-- imply
  ∀ {f rho : Real → Real} {C : NNReal} {B a b : Real} (hf : Continuous f) (hlip : LipschitzWith C f) (hrho : Continuous rho) (hB : 0 <= B) (hrhoBound : ∀ x ∈ Set.uIcc a b, |rho x| <= B) (hab : a <= b), |f a * (∫ x in a..b, rho x) - ∫ x in a..b, f x * rho x| <= (C : Real) * B * (b - a) ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_left_mul_densityIntegral_sub_integral_mul_le

/--
[abs_weightedLeftEndpointSum_sub_densityIntegral_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWeightedQuadrature.lean)
-/
@[path]
private lemma abs_weightedLeftEndpointSum_sub_densityIntegral_le_eq :
-- imply
  ∀ {f rho : Real → Real} {C : NNReal} {B mesh : Real} (hf : Continuous f) (hlip : LipschitzWith C f) (hrho : Continuous rho) (hB : 0 <= B) (a : Nat → Real) (mass : Nat → Real) (n : Nat) (hordered : ∀ k < n, a k <= a (k + 1)) (hmesh : ∀ k < n, a (k + 1) - a k <= mesh) (hrhoBound : ∀ x, |rho x| <= B) (hmass : ∀ k < n, ∫ x in a k..a (k + 1), rho x = mass k), |∑ k ∈ Finset.range n, mass k * f (a k) - ∫ x in a 0..a n, f x * rho x| <= (C : Real) * B * mesh * (a n - a 0) := by
-- proof
  apply StatMech.FrontierD.abs_weightedLeftEndpointSum_sub_densityIntegral_le


-- created on 2026-10-23
