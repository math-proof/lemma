import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheQuadrature
open MeasureTheory StatMech StatMech.FrontierD


/--
[abs_gap_mul_left_sub_intervalIntegral_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheQuadrature.lean)
-/
@[path]
private lemma abs_gap_mul_left_sub_intervalIntegral_le_eq :
-- imply
  ∀ {f : Real → Real} {C : NNReal} (hf : Continuous f) (hlip : LipschitzWith C f) {a b : Real} (hab : a ≤ b), |(b - a) * f a - ∫ x in a..b, f x| ≤ (C : Real) * (b - a) ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_gap_mul_left_sub_intervalIntegral_le

/--
[abs_gap_mul_right_sub_intervalIntegral_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheQuadrature.lean)
-/
@[path]
private lemma abs_gap_mul_right_sub_intervalIntegral_le_eq :
-- imply
  ∀ {f : Real → Real} {C : NNReal} (hf : Continuous f) (hlip : LipschitzWith C f) {a b : Real} (hab : a ≤ b), |(b - a) * f b - ∫ x in a..b, f x| ≤ 2 * (C : Real) * (b - a) ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_gap_mul_right_sub_intervalIntegral_le

/--
[abs_leftEndpointSum_sub_intervalIntegral_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheQuadrature.lean)
-/
@[path]
private lemma abs_leftEndpointSum_sub_intervalIntegral_le_eq :
-- imply
  ∀ {f : Real → Real} {C : NNReal} (hf : Continuous f) (hlip : LipschitzWith C f) (a : Nat → Real) (n : Nat) {mesh : Real} (hordered : ∀ k < n, a k ≤ a (k + 1)) (hmesh : ∀ k < n, a (k + 1) - a k ≤ mesh), |∑ k ∈ Finset.range n, (a (k + 1) - a k) * f (a k) - ∫ x in a 0..a n, f x| ≤ (C : Real) * mesh * (a n - a 0) := by
-- proof
  apply StatMech.FrontierD.abs_leftEndpointSum_sub_intervalIntegral_le


-- created on 2026-10-23
