import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeNonperiodicQuadrature.Part2
open Finset StatMech StatMech.FrontierD


/--
[sum_cyclicRootPartition_eq_sum_roots_add_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeNonperiodicQuadrature.lean)
-/
@[path]
private lemma sum_cyclicRootPartition_eq_sum_roots_add_boundary_eq
  {n : Nat}
-- given
  (p : Fin (n + 1) -> Real)
  (f : Real -> Real) :
-- imply
  (∑ k ∈ range (n + 1), f (sixVertexCyclicRootPartition p k)) = (∑ j, f (p j)) + f (p (Fin.last n) - 2 * Real.pi) - f (p (Fin.last n)) := by
-- proof
  apply StatMech.FrontierD.sum_cyclicRootPartition_eq_sum_roots_add_boundary p f

/--
[abs_empiricalLipschitz_sub_finiteDensityIntegral_fixedCharge_nonperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeNonperiodicQuadrature.lean)
-/
@[path]
private lemma abs_empiricalLipschitz_sub_finiteDensityIntegral_fixedCharge_nonperiodic_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin (n + 1) -> Real}
  {lower : Real}
  {f : Real -> Real}
  {C : NNReal}
  {F : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcharge : N = 2 * (n + 1) + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N (n + 1) p x)
  (hf : Continuous f)
  (hlip : LipschitzWith C f)
  (hfBound : forall x, |f x| <= F) :
-- imply
  |(∑ j, f (p j)) / N - ∫ y in -Real.pi..Real.pi, f y * sixVertexFiniteRootDensity c N (n + 1) p y| <= (C : Real) * sixVertexFiniteRootDensityUniformBound c * ((2 * (r : Real) + 1) / ((N : Real) * lower)) * (2 * Real.pi) + (2 * (r : Real) / N) * F + 2 * F / N + sixVertexFiniteRootDensityUniformBound c * F * ((2 * (r : Real) + 1) / ((N : Real) * lower)) := by
-- proof
  apply StatMech.FrontierD.abs_empiricalLipschitz_sub_finiteDensityIntegral_fixedCharge_nonperiodic hc hN hcharge hopen hsol hlower hdensity hf hlip hfBound

/--
[abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz_nonperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeNonperiodicQuadrature.lean)
-/
@[path]
private lemma abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz_nonperiodic_eq
  {c : Real}
  {N m r : Nat}
  {p : Fin m -> Real}
  {lower : Real}
  {x : Real}
  {tau : Real -> Real}
  {D : NNReal}
  {G : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hm : 0 < m)
  (hcharge : N = 2 * m + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N m p)
  (hlower : 0 < lower)
  (hdensity : forall y, lower <= sixVertexFiniteRootDensity c N m p y)
  (htauLip : LipschitzWith D tau)
  (htauBound : forall y, |tau y| <= G) :
-- imply
  |(∑ j, sixVertexContinuousOffsetKernel c x (p j) * tau (p j) / sixVertexFiniteRootDensity c N m p (p j)) / N - ∫ y in -Real.pi..Real.pi, sixVertexContinuousOffsetKernel c x y * tau y| <= sixVertexFixedChargeNonperiodicOffsetTestError c N r lower G D := by
-- proof
  apply StatMech.FrontierD.abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz_nonperiodic hc hN hm hcharge hopen hsol hlower hdensity x htauLip htauBound

/--
[tendsto_sixVertexFixedChargeNonperiodicOffsetTestError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeNonperiodicQuadrature.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeNonperiodicOffsetTestError_eq
  {c : Real}
  {r : Nat}
  {lower : Real}
  {G : Real}
  {D : NNReal}
-- given
  (hlower : 0 < lower) :
-- imply
  Filter.Tendsto (fun k => sixVertexFixedChargeNonperiodicOffsetTestError c (sixVertexFourWidth r k) r lower G D) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeNonperiodicOffsetTestError c r hlower G D


-- created on 2026-10-23
