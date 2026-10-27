import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetTaylor
open StatMech StatMech.FrontierD


/--
[coe_sixVertexThetaDerivativeLipschitzNNReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetTaylor.lean)
-/
@[path]
private lemma coe_sixVertexThetaDerivativeLipschitzNNReal_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  (sixVertexThetaDerivativeLipschitzNNReal c : Real) = sixVertexThetaLeftKernelLipschitzBound c := by
-- proof
  apply StatMech.FrontierD.coe_sixVertexThetaDerivativeLipschitzNNReal hc

/--
[lipschitzWith_sixVertexThetaLeftDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetTaylor.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexThetaLeftDerivative_eq
  {c : Real}
  {y : Real}
-- given
  (hc : 2 < c) :
-- imply
  LipschitzWith (sixVertexThetaDerivativeLipschitzNNReal c) (fun x => 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y / sixVertexThetaDerivativeDenominator c x y) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexThetaLeftDerivative hc y

/--
[lipschitzWith_sixVertexThetaRightDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetTaylor.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexThetaRightDerivative_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  LipschitzWith (sixVertexThetaDerivativeLipschitzNNReal c) (fun y => -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x / sixVertexThetaDerivativeDenominator c x y) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexThetaRightDerivative hc x

/--
[abs_intervalIntegral_sub_const_mul_le_of_lipschitz'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetTaylor.lean)
-/
@[path]
private lemma abs_intervalIntegral_sub_const_mul_le_of_lipschitz'_eq
  {f : Real → Real}
  {C : NNReal}
  {a b u : Real}
-- given
  (hf : Continuous f)
  (hlip : LipschitzWith C f)
  (hu : u ∈ Set.uIcc a b) :
-- imply
  |(∫ x in a..b, f x) - f u * (b - a)| ≤ (C : Real) * |b - a| ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_intervalIntegral_sub_const_mul_le_of_lipschitz' hf hlip a b u hu

/--
[abs_sub_sub_deriv_mul_le_of_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetTaylor.lean)
-/
@[path]
private lemma abs_sub_sub_deriv_mul_le_of_lipschitz_eq
  {f f' : Real → Real}
  {C : NNReal}
  {a b : Real}
-- given
  (hderiv : ∀ x, HasDerivAt f (f' x) x)
  (hlip : LipschitzWith C f') :
-- imply
  |f b - f a - f' a * (b - a)| ≤ (C : Real) * |b - a| ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_sub_sub_deriv_mul_le_of_lipschitz hderiv hlip a b

/--
[abs_sixVertexThetaLeftDerivative_sub_right_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetTaylor.lean)
-/
@[path]
private lemma abs_sixVertexThetaLeftDerivative_sub_right_le_eq
  {c : Real}
  {x y z : Real}
-- given
  (hc : 2 < c) :
-- imply
  |4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y / sixVertexThetaDerivativeDenominator c x y - 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c z / sixVertexThetaDerivativeDenominator c x z| ≤ sixVertexThetaCrossLipschitzBound c * |y - z| := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexThetaLeftDerivative_sub_right_le hc x y z

/--
[abs_sixVertexTheta_sub_linearization_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetTaylor.lean)
-/
@[path]
private lemma abs_sixVertexTheta_sub_linearization_le_eq
  {c : Real}
  {x y x' y' : Real}
-- given
  (hc : 2 < c) :
-- imply
  |sixVertexTheta c x' y' - sixVertexTheta c x y - ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y / sixVertexThetaDerivativeDenominator c x y) * (x' - x) + (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x / sixVertexThetaDerivativeDenominator c x y) * (y' - y))| ≤ sixVertexThetaTaylorBound c * (|x' - x| + |y' - y|) ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexTheta_sub_linearization_le hc x y x' y'

/--
[abs_sum_sixVertexTheta_sub_linearization_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetTaylor.lean)
-/
@[path]
private lemma abs_sum_sixVertexTheta_sub_linearization_le_eq
  {c : Real}
  {N n : Nat}
  {p q : Fin n → Real}
  {B : Real}
  {i : Fin n}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : n ≤ N)
  (hB : 0 ≤ B)
  (hoffset : ∀ j, |(N : Real) * (q j - p j)| ≤ B) :
-- imply
  |∑ j, (sixVertexTheta c (p i) (p j) - sixVertexTheta c (q i) (q j) - ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) / sixVertexThetaDerivativeDenominator c (q i) (q j)) * (p i - q i) + (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q i) / sixVertexThetaDerivativeDenominator c (q i) (q j)) * (p j - q j)))| ≤ 4 * sixVertexThetaTaylorBound c * B ^ 2 / N := by
-- proof
  apply StatMech.FrontierD.abs_sum_sixVertexTheta_sub_linearization_le hc hN hn hB hoffset i


-- created on 2026-10-23
