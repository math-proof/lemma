import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetNodal.Part3
open StatMech StatMech.FrontierD


/--
[sixVertexCanonicalEvenOffsetNodalResidual_eq_weightedConvolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean)
-/
@[path]
private lemma sixVertexCanonicalEvenOffsetNodalResidual_eq_weightedConvolution_eq
  {c : Real}
  {s k : Nat}
  {j : Fin ((s + k + 1) + (s + k + 1))}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalEvenOffsetNodalResidual hc s k j = 2 * Real.pi * (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) * sixVertexCanonicalEvenChargeOffset hc s k j) - sixVertexCanonicalEvenOffsetBoundarySource hc s k j + (1 / (sixVertexFourWidth (2 * s) k : Real)) * ∑ l, sixVertexContinuousOffsetKernel c (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l) * sixVertexCanonicalEvenChargeOffset hc s k l := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalEvenOffsetNodalResidual_eq_weightedConvolution hc s k j

/--
[sixVertexCanonicalOddOffsetNodalResidual_eq_weightedConvolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean)
-/
@[path]
private lemma sixVertexCanonicalOddOffsetNodalResidual_eq_weightedConvolution_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (((s + k + 1) + 1) + (s + k + 1))}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalOddOffsetNodalResidual hc s k j = 2 * Real.pi * (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) * sixVertexCanonicalOddChargeOffset hc s k j) - sixVertexCanonicalOddOffsetBoundarySource hc s k j + (1 / (sixVertexFourWidth (2 * s + 1) k : Real)) * ∑ l, sixVertexContinuousOffsetKernel c (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l) * sixVertexCanonicalOddChargeOffset hc s k l := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddOffsetNodalResidual_eq_weightedConvolution hc s k j

/--
[empiricalContinuousOffsetKernel_le_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean)
-/
@[path]
private lemma empiricalContinuousOffsetKernel_le_of_lower_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin n -> Real}
  {lower : Real}
  {i : Fin n}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : 0 < n)
  (hcharge : N = 2 * n + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N n p)
  (hlower : 0 < lower)
  (hdensity : forall y, lower <= sixVertexFiniteRootDensity c N n p y) :
-- imply
  (1 / (N : Real)) * ∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) / sixVertexFiniteRootDensity c N n p (p j) <= 2 * Real.pi + sixVertexFixedChargeOffsetRowError c N r lower := by
-- proof
  apply StatMech.FrontierD.empiricalContinuousOffsetKernel_le_of_lower hc hN hn hcharge hopen hsol hlower hdensity i

/--
[tendsto_sixVertexFixedChargeOffsetRowError_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeOffsetRowError_of_lower_eq
  {c lower : Real}
  {r : Nat}
-- given
  (hlower : 0 < lower) :
-- imply
  Tendsto (fun k => sixVertexFixedChargeOffsetRowError c (sixVertexFourWidth r k) r lower) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeOffsetRowError_of_lower hlower r

/--
[tendsto_sixVertexCanonicalOffsetNetMargin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOffsetNetMargin_eq
  {c lower : Real}
  {r : Nat}
-- given
  (hlower : 0 < lower) :
-- imply
  Tendsto (fun k => sixVertexCanonicalOffsetNetMargin c (sixVertexFourWidth r k) r lower) atTop (nhds (sixVertexFixedChargeOffsetContractionMargin c)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOffsetNetMargin hlower r

/--
[eventually_sixVertexCanonicalOffsetNetMargin_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalOffsetNetMargin_pos_eq
  {c lower : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower) :
-- imply
  ∀ᶠ k : Nat in atTop, 0 < sixVertexCanonicalOffsetNetMargin c (sixVertexFourWidth r k) r lower := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalOffsetNetMargin_pos hc hlower r

/--
[abs_sixVertexCanonicalEvenDensityOffset_sub_continuous_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalEvenDensityOffset_sub_continuous_le_eq
  {c : Real}
  {s k : Nat}
  {tau : Real -> Real}
  {testError : Real}
  {i : Fin ((s + k + 1) + (s + k + 1))}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexCanonicalFixedEvenDensityWitness hc s k (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))
  (hhalf : forall y, sixVertexCanonicalHalfDensityFloor hc <= sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + k)) ((2 * s + k + 1) + (2 * s + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k)) y)
  (htauOdd : Function.Odd tau)
  (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
  (hquad : forall i : Fin ((s + k + 1) + (s + k + 1)), |(∑ l, sixVertexContinuousOffsetKernel c (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l) * tau (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l) / sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l)) / sixVertexFourWidth (2 * s) k - ∫ y in -Real.pi..Real.pi, sixVertexContinuousOffsetKernel c (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i) y * tau y| <= testError)
  (hoffset : forall j, |sixVertexCanonicalEvenChargeOffset hc s k j| <= sixVertexCanonicalEvenOffsetUniformBound c hc s)
  (hmargin : 0 < sixVertexCanonicalOffsetNetMargin c (sixVertexFourWidth (2 * s) k) (2 * s) (sixVertexCanonicalFixedEvenDensityFloor hc s)) :
-- imply
  |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i) * sixVertexCanonicalEvenChargeOffset hc s k i - (2 * s : Real) * tau (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i)| <= sixVertexCanonicalEvenOffsetNodalError c hc s (sixVertexFourWidth (2 * s) k) testError / sixVertexCanonicalOffsetNetMargin c (sixVertexFourWidth (2 * s) k) (2 * s) (sixVertexCanonicalFixedEvenDensityFloor hc s) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalEvenDensityOffset_sub_continuous_le hc s k hfixed hhalf htauOdd htauEq hquad hoffset hmargin i

/--
[abs_sixVertexCanonicalOddDensityOffset_sub_continuous_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalOddDensityOffset_sub_continuous_le_eq
  {c : Real}
  {s k : Nat}
  {tau : Real -> Real}
  {testError : Real}
  {i : Fin (((s + k + 1) + 1) + (s + k + 1))}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k))
  (hhalf : forall y, sixVertexCanonicalHalfDensityFloor hc <= sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + 1 + k)) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) y)
  (htauOdd : Function.Odd tau)
  (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
  (hquad : forall i : Fin (((s + k + 1) + 1) + (s + k + 1)), |(∑ l, sixVertexContinuousOffsetKernel c (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l) * tau (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l) / sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l)) / sixVertexFourWidth (2 * s + 1) k - ∫ y in -Real.pi..Real.pi, sixVertexContinuousOffsetKernel c (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i) y * tau y| <= testError)
  (hoffset : forall j, |sixVertexCanonicalOddChargeOffset hc s k j| <= sixVertexCanonicalOddOffsetUniformBound c hc s)
  (hmargin : 0 < sixVertexCanonicalOffsetNetMargin c (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1) (sixVertexCanonicalFixedOddDensityFloor hc s)) :
-- imply
  |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i) * sixVertexCanonicalOddChargeOffset hc s k i - (2 * s + 1 : Real) * tau (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i)| <= sixVertexCanonicalOddOffsetNodalError c hc s (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) testError / sixVertexCanonicalOffsetNetMargin c (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1) (sixVertexCanonicalFixedOddDensityFloor hc s) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalOddDensityOffset_sub_continuous_le hc s k hfixed hhalf htauOdd htauEq hquad hoffset hmargin i

/--
[tendsto_sixVertexCanonicalEvenOffsetNodalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalEvenOffsetNodalError_eq
  {c : Real}
  {s : Nat}
  {G : Real}
  {D : NNReal}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalEvenOffsetNodalError c hc s (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeNonperiodicOffsetTestError c (sixVertexFourWidth (2 * s) k) (2 * s) (sixVertexCanonicalFixedEvenDensityFloor hc s) G D)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalEvenOffsetNodalError hc s G D

/--
[tendsto_sixVertexCanonicalOddOffsetNodalError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddOffsetNodalError_eq
  {c : Real}
  {s : Nat}
  {G : Real}
  {D : NNReal}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalOddOffsetNodalError c hc s (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexFixedChargeNonperiodicOffsetTestError c (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1) (sixVertexCanonicalFixedOddDensityFloor hc s) G D)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddOffsetNodalError hc s G D

/--
[eventually_uniform_sixVertexCanonicalEvenDensityOffset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean)
-/
@[path]
private lemma eventually_uniform_sixVertexCanonicalEvenDensityOffset_eq
  {c : Real}
  {s : Nat}
  {tau : Real -> Real}
  {D : NNReal}
  {G : Real}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (htauLip : LipschitzWith D tau)
  (htauBound : forall y, |tau y| <= G)
  (htauOdd : Function.Odd tau)
  (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
  (hepsilon : 0 < epsilon) :
-- imply
  ∀ᶠ k : Nat in atTop, forall i : Fin ((s + k + 1) + (s + k + 1)), |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i) * sixVertexCanonicalEvenChargeOffset hc s k i - (2 * s : Real) * tau (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i)| < epsilon := by
-- proof
  apply StatMech.FrontierD.eventually_uniform_sixVertexCanonicalEvenDensityOffset hc s htauLip htauBound htauOdd htauEq hepsilon

/--
[eventually_uniform_sixVertexCanonicalOddDensityOffset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean)
-/
@[path]
private lemma eventually_uniform_sixVertexCanonicalOddDensityOffset_eq
  {c : Real}
  {s : Nat}
  {tau : Real -> Real}
  {D : NNReal}
  {G : Real}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (htauLip : LipschitzWith D tau)
  (htauBound : forall y, |tau y| <= G)
  (htauOdd : Function.Odd tau)
  (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
  (hepsilon : 0 < epsilon) :
-- imply
  ∀ᶠ k : Nat in atTop, forall i : Fin (((s + k + 1) + 1) + (s + k + 1)), |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i) * sixVertexCanonicalOddChargeOffset hc s k i - (2 * s + 1 : Real) * tau (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i)| < epsilon := by
-- proof
  apply StatMech.FrontierD.eventually_uniform_sixVertexCanonicalOddDensityOffset hc s htauLip htauBound htauOdd htauEq hepsilon


-- created on 2026-10-23
