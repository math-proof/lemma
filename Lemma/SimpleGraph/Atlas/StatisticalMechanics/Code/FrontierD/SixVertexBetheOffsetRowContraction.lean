import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetRowContraction
open StatMech StatMech.FrontierD


/--
[sixVertexFixedChargeOffsetContractionMargin_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetRowContraction.lean)
-/
@[path]
private lemma sixVertexFixedChargeOffsetContractionMargin_pos_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexFixedChargeOffsetContractionMargin c := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeOffsetContractionMargin_pos hc

/--
[tendsto_sixVertexFixedChargeOffsetRowError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetRowContraction.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeOffsetRowError_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k => sixVertexFixedChargeOffsetRowError c (sixVertexFourWidth r k) r (sixVertexTailFiniteDensityFloor c)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeOffsetRowError hc htail r

/--
[eventually_sixVertexFixedChargeOffsetRowError_le_halfMargin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetRowContraction.lean)
-/
@[path]
private lemma eventually_sixVertexFixedChargeOffsetRowError_le_halfMargin_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexFixedChargeOffsetRowError c (sixVertexFourWidth r k) r (sixVertexTailFiniteDensityFloor c) ≤ sixVertexFixedChargeOffsetContractionMargin c / 2 := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexFixedChargeOffsetRowError_le_halfMargin hc htail r

/--
[abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetRowContraction.lean)
-/
@[path]
private lemma abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_eq
  {c : Real}
  {N m r : Nat}
  {p : Fin m → Real}
  {lower : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hm : 0 < m)
  (hcharge : N = 2 * m + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N m p)
  (hlower : 0 < lower)
  (hdensity : ∀ y, lower ≤ sixVertexFiniteRootDensity c N m p y) :
-- imply
  |(∑ j, sixVertexContinuousOffsetKernel c x (p j) / sixVertexFiniteRootDensity c N m p (p j)) / N - ∫ y in -Real.pi..Real.pi, sixVertexContinuousOffsetKernel c x y| ≤ sixVertexFixedChargeOffsetRowError c N r lower := by
-- proof
  apply StatMech.FrontierD.abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos hc hN hm hcharge hopen hsol hlower hdensity x

/--
[empiricalContinuousOffsetKernel_fixedCharge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetRowContraction.lean)
-/
@[path]
private lemma empiricalContinuousOffsetKernel_fixedCharge_le_eq
  {c : Real}
  {r k : Nat}
  {i : Fin (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  (1 / (sixVertexFourWidth r k : Real)) * ∑ j, sixVertexContinuousOffsetKernel c (sixVertexFixedChargeBetheRoots hc r k i) (sixVertexFixedChargeBetheRoots hc r k j) / sixVertexFiniteRootDensity c (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) (sixVertexFixedChargeBetheRoots hc r k) (sixVertexFixedChargeBetheRoots hc r k j) ≤ 2 * Real.pi + sixVertexFixedChargeOffsetRowError c (sixVertexFourWidth r k) r (sixVertexTailFiniteDensityFloor c) := by
-- proof
  apply StatMech.FrontierD.empiricalContinuousOffsetKernel_fixedCharge_le hc htail r k i

/--
[reciprocalWeightDensityMass_fixedCharge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetRowContraction.lean)
-/
@[path]
private lemma reciprocalWeightDensityMass_fixedCharge_le_eq
  {c : Real}
  {r k : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  sixVertexRootDensityScale c / (4 * (sixVertexAnisotropyMagnitude c + 1) * sixVertexFiniteRootDensityUniformBound c) ≤ (1 / (sixVertexFourWidth r k : Real)) * ∑ j, 1 / (sixVertexRootDensityWeight c (sixVertexFixedChargeBetheRoots hc r k j) * sixVertexFiniteRootDensity c (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) (sixVertexFixedChargeBetheRoots hc r k) (sixVertexFixedChargeBetheRoots hc r k j)) := by
-- proof
  apply StatMech.FrontierD.reciprocalWeightDensityMass_fixedCharge_le hc htail r k

/--
[abs_empiricalContinuousOffsetKernel_mul_fixedCharge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetRowContraction.lean)
-/
@[path]
private lemma abs_empiricalContinuousOffsetKernel_mul_fixedCharge_le_eq
  {c : Real}
  {r k : Nat}
  {e : Fin (sixVertexFixedChargeBetheParticleCount r k) → Real}
  {E : Real}
  {i : Fin (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hE : 0 ≤ E)
  (he : ∀ j, |e j| ≤ E)
  (hmass : (1 / (sixVertexFourWidth r k : Real)) * ∑ j, e j / (sixVertexRootDensityWeight c (sixVertexFixedChargeBetheRoots hc r k j) * sixVertexFiniteRootDensity c (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) (sixVertexFixedChargeBetheRoots hc r k) (sixVertexFixedChargeBetheRoots hc r k j)) = 0) :
-- imply
  |(1 / (sixVertexFourWidth r k : Real)) * ∑ j, sixVertexContinuousOffsetKernel c (sixVertexFixedChargeBetheRoots hc r k i) (sixVertexFixedChargeBetheRoots hc r k j) / sixVertexFiniteRootDensity c (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) (sixVertexFixedChargeBetheRoots hc r k) (sixVertexFixedChargeBetheRoots hc r k j) * e j| ≤ (2 * Real.pi + sixVertexFixedChargeOffsetRowError c (sixVertexFourWidth r k) r (sixVertexTailFiniteDensityFloor c) - sixVertexFixedChargeOffsetContractionMargin c) * E := by
-- proof
  apply StatMech.FrontierD.abs_empiricalContinuousOffsetKernel_mul_fixedCharge_le hc htail r k hE he hmass i


-- created on 2026-10-23
