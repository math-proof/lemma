import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalRegularizedQuadrature
open StatMech StatMech.FrontierD


/--
[tendsto_sixVertexLogNonperiodicQuadratureError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalRegularizedQuadrature.lean)
-/
@[path]
private lemma tendsto_sixVertexLogNonperiodicQuadratureError_eq
  {c : Real}
  {r : Nat}
  {lower : Real}
  {C : NNReal}
  {F : Real}
-- given
  (hlower : 0 < lower) :
-- imply
  Tendsto (fun k => sixVertexLogNonperiodicQuadratureError c (sixVertexFourWidth r k) r lower C F) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexLogNonperiodicQuadratureError c r hlower C F

/--
[tendsto_sixVertexCanonicalEvenRegularizedDerivativeProfileQuotient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalRegularizedQuadrature.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalEvenRegularizedDerivativeProfileQuotient_eq
  {c : Real}
  {s : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Tendsto (fun k => (∑ j, sixVertexRegularizedBetheLogNormDerivative c epsilon (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) * sixVertexContinuousOffsetFourier c hc (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) / sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j)) / (sixVertexFourWidth (2 * s) k : Real)) atTop (nhds (∫ x in -Real.pi..Real.pi, sixVertexRegularizedBetheLogNormDerivative c epsilon x * sixVertexContinuousOffsetFourier c hc x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalEvenRegularizedDerivativeProfileQuotient hc s hepsilon

/--
[tendsto_sixVertexCanonicalOddRegularizedDerivativeProfileQuotient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalRegularizedQuadrature.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddRegularizedDerivativeProfileQuotient_eq
  {c : Real}
  {s : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Tendsto (fun k => (∑ j, sixVertexRegularizedBetheLogNormDerivative c epsilon (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) * sixVertexContinuousOffsetFourier c hc (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) / sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j)) / (sixVertexFourWidth (2 * s + 1) k : Real)) atTop (nhds (∫ x in -Real.pi..Real.pi, sixVertexRegularizedBetheLogNormDerivative c epsilon x * sixVertexContinuousOffsetFourier c hc x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddRegularizedDerivativeProfileQuotient hc s hepsilon

/--
[tendsto_sixVertexCanonicalEvenRegularizedLinearizedOffset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalRegularizedQuadrature.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalEvenRegularizedLinearizedOffset_eq
  {c : Real}
  {s : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Tendsto (fun k => (∑ j, sixVertexRegularizedBetheLogNormDerivative c epsilon (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) * sixVertexCanonicalEvenChargeOffset hc s k j) / (sixVertexFourWidth (2 * s) k : Real)) atTop (nhds ((2 * s : Real) * ∫ x in -Real.pi..Real.pi, sixVertexRegularizedBetheLogNormDerivative c epsilon x * sixVertexContinuousOffsetFourier c hc x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalEvenRegularizedLinearizedOffset hc s hepsilon

/--
[tendsto_sixVertexCanonicalEvenRegularizedRootDisplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalRegularizedQuadrature.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalEvenRegularizedRootDisplacement_eq
  {c : Real}
  {s : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Tendsto (fun k => ∑ j, (sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) - sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalEvenAlignedHalfRoots hc s k j))) atTop (nhds ((2 * s : Real) * ∫ x in -Real.pi..Real.pi, sixVertexRegularizedBetheLogNormDerivative c epsilon x * sixVertexContinuousOffsetFourier c hc x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalEvenRegularizedRootDisplacement hc s hepsilon

/--
[sum_sixVertexCanonicalEvenRegularizedRootDisplacement_eq_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalRegularizedQuadrature.lean)
-/
@[path]
private lemma sum_sixVertexCanonicalEvenRegularizedRootDisplacement_eq_positive_eq
  {c : Real}
  {s k : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexCanonicalFixedEvenDensityWitness hc s k (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)) :
-- imply
  (∑ j, (sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) - sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalEvenAlignedHalfRoots hc s k j))) = 2 * ∑ j, (sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) - sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalEvenCommonHalfRoot hc s k j)) := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexCanonicalEvenRegularizedRootDisplacement_eq_positive hc s k epsilon hfixed

/--
[tendsto_sixVertexCanonicalEvenPositiveRegularizedRootDisplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalRegularizedQuadrature.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalEvenPositiveRegularizedRootDisplacement_eq
  {c : Real}
  {s : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Tendsto (fun k => 2 * ∑ j, (sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) - sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalEvenCommonHalfRoot hc s k j))) atTop (nhds ((2 * s : Real) * ∫ x in -Real.pi..Real.pi, sixVertexRegularizedBetheLogNormDerivative c epsilon x * sixVertexContinuousOffsetFourier c hc x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalEvenPositiveRegularizedRootDisplacement hc s hepsilon

/--
[tendsto_sixVertexCanonicalOddRegularizedLinearizedOffset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalRegularizedQuadrature.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddRegularizedLinearizedOffset_eq
  {c : Real}
  {s : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Tendsto (fun k => (∑ j, sixVertexRegularizedBetheLogNormDerivative c epsilon (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) * sixVertexCanonicalOddChargeOffset hc s k j) / (sixVertexFourWidth (2 * s + 1) k : Real)) atTop (nhds ((2 * s + 1 : Real) * ∫ x in -Real.pi..Real.pi, sixVertexRegularizedBetheLogNormDerivative c epsilon x * sixVertexContinuousOffsetFourier c hc x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddRegularizedLinearizedOffset hc s hepsilon

/--
[tendsto_sixVertexCanonicalOddRegularizedRootDisplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalRegularizedQuadrature.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddRegularizedRootDisplacement_eq
  {c : Real}
  {s : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Tendsto (fun k => ∑ j, (sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) - sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalOddAlignedHalfRoots hc s k j))) atTop (nhds ((2 * s + 1 : Real) * ∫ x in -Real.pi..Real.pi, sixVertexRegularizedBetheLogNormDerivative c epsilon x * sixVertexContinuousOffsetFourier c hc x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddRegularizedRootDisplacement hc s hepsilon

/--
[sum_sixVertexCanonicalOddRegularizedRootDisplacement_eq_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalRegularizedQuadrature.lean)
-/
@[path]
private lemma sum_sixVertexCanonicalOddRegularizedRootDisplacement_eq_positive_eq
  {c : Real}
  {s k : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
-- imply
  (∑ j, (sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) - sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalOddAlignedHalfRoots hc s k j))) = 2 * ∑ j, (sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) - sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexCanonicalOddRegularizedRootDisplacement_eq_positive hc s k epsilon hfixed

/--
[tendsto_sixVertexCanonicalOddPositiveRegularizedRootDisplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalRegularizedQuadrature.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddPositiveRegularizedRootDisplacement_eq
  {c : Real}
  {s : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Tendsto (fun k => 2 * ∑ j, (sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) - sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalOddMidpointHalfRoot hc s k j))) atTop (nhds ((2 * s + 1 : Real) * ∫ x in -Real.pi..Real.pi, sixVertexRegularizedBetheLogNormDerivative c epsilon x * sixVertexContinuousOffsetFourier c hc x)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddPositiveRegularizedRootDisplacement hc s hepsilon


-- created on 2026-10-23
