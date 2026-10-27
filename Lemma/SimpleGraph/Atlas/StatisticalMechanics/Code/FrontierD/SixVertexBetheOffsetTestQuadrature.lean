import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetTestQuadrature
open StatMech StatMech.FrontierD


/--
[abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetTestQuadrature.lean)
-/
@[path]
private lemma abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz_eq
  {c : Real}
  {N m r : Nat}
  {p : Fin m → Real}
  {lower : Real}
  {x : Real}
  {tau : Real → Real}
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
  (hdensity : ∀ y, lower ≤ sixVertexFiniteRootDensity c N m p y)
  (htauLip : LipschitzWith D tau)
  (htauPeriodic : Function.Periodic tau (2 * Real.pi))
  (htauBound : ∀ y, |tau y| ≤ G) :
-- imply
  |(∑ j, sixVertexContinuousOffsetKernel c x (p j) * tau (p j) / sixVertexFiniteRootDensity c N m p (p j)) / N - ∫ y in -Real.pi..Real.pi, sixVertexContinuousOffsetKernel c x y * tau y| ≤ sixVertexFixedChargeOffsetTestError c N r lower G D := by
-- proof
  apply StatMech.FrontierD.abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz hc hN hm hcharge hopen hsol hlower hdensity x htauLip htauPeriodic htauBound

/--
[tendsto_sixVertexFixedChargeOffsetTestError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetTestQuadrature.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeOffsetTestError_eq
  {c : Real}
  {r : Nat}
  {lower : Real}
  {G : Real}
  {D : NNReal}
-- given
  (hlower : 0 < lower) :
-- imply
  Tendsto (fun k => sixVertexFixedChargeOffsetTestError c (sixVertexFourWidth r k) r lower G D) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeOffsetTestError c r hlower G D


-- created on 2026-10-23
