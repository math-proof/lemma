import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetOperatorQuadrature
open StatMech StatMech.FrontierD


/--
[periodic_sixVertexRootDensityWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetOperatorQuadrature.lean)
-/
@[path]
private lemma periodic_sixVertexRootDensityWeight_eq
  {c : Real} :
-- imply
  Function.Periodic (sixVertexRootDensityWeight c) (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.periodic_sixVertexRootDensityWeight c

/--
[periodic_sixVertexContinuousOffsetKernel_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetOperatorQuadrature.lean)
-/
@[path]
private lemma periodic_sixVertexContinuousOffsetKernel_right_eq
  {c x : Real} :
-- imply
  Function.Periodic (sixVertexContinuousOffsetKernel c x) (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.periodic_sixVertexContinuousOffsetKernel_right c x

/--
[lipschitzWith_sixVertexContinuousOffsetKernel_mul_div_finiteDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetOperatorQuadrature.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexContinuousOffsetKernel_mul_div_finiteDensity_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {lower G : Real}
  {tau : Real → Real}
  {D : NNReal}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : n ≤ N)
  (hlower : 0 < lower)
  (hdensity : ∀ y, lower ≤ sixVertexFiniteRootDensity c N n p y)
  (htauLip : LipschitzWith D tau)
  (htauBound : ∀ y, |tau y| ≤ G) :
-- imply
  LipschitzWith (sixVertexOffsetQuotientLipschitzNNReal c lower G D) (fun y => sixVertexContinuousOffsetKernel c x y * tau y / sixVertexFiniteRootDensity c N n p y) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexContinuousOffsetKernel_mul_div_finiteDensity hc hN hn p hlower hdensity htauLip htauBound x

/--
[abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetOperatorQuadrature.lean)
-/
@[path]
private lemma abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin (n + 1) → Real}
  {lower : Real}
  {x : Real}
  {tau : Real → Real}
  {C : NNReal}
  {G : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcharge : N = 2 * (n + 1) + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hlower : 0 < lower)
  (hdensity : ∀ y, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p y)
  (htau : Continuous tau)
  (htauPeriodic : Function.Periodic tau (2 * Real.pi))
  (htauBound : ∀ y, |tau y| ≤ G)
  (hlip : LipschitzWith C (fun y => sixVertexContinuousOffsetKernel c x y * tau y / sixVertexFiniteRootDensity c N (n + 1) p y)) :
-- imply
  |(∑ j, sixVertexContinuousOffsetKernel c x (p j) * tau (p j) / sixVertexFiniteRootDensity c N (n + 1) p (p j)) / N - ∫ y in -Real.pi..Real.pi, sixVertexContinuousOffsetKernel c x y * tau y| ≤ (C : Real) * sixVertexFiniteRootDensityUniformBound c * ((2 * (r : Real) + 1) / ((N : Real) * lower)) * (2 * Real.pi) + (2 * (r : Real) / N) * ((sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1)) * G / lower) := by
-- proof
  apply StatMech.FrontierD.abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge hc hN hcharge hopen hsol hlower hdensity x htau htauPeriodic htauBound hlip

/--
[abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_of_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetOperatorQuadrature.lean)
-/
@[path]
private lemma abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_of_lipschitz_eq
  {c : Real}
  {N n r : Nat}
  {p : Fin (n + 1) → Real}
  {lower : Real}
  {x : Real}
  {tau : Real → Real}
  {D : NNReal}
  {G : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcharge : N = 2 * (n + 1) + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hlower : 0 < lower)
  (hdensity : ∀ y, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p y)
  (htauLip : LipschitzWith D tau)
  (htauPeriodic : Function.Periodic tau (2 * Real.pi))
  (htauBound : ∀ y, |tau y| ≤ G) :
-- imply
  |(∑ j, sixVertexContinuousOffsetKernel c x (p j) * tau (p j) / sixVertexFiniteRootDensity c N (n + 1) p (p j)) / N - ∫ y in -Real.pi..Real.pi, sixVertexContinuousOffsetKernel c x y * tau y| ≤ (sixVertexOffsetQuotientLipschitzNNReal c lower G D : Real) * sixVertexFiniteRootDensityUniformBound c * ((2 * (r : Real) + 1) / ((N : Real) * lower)) * (2 * Real.pi) + (2 * (r : Real) / N) * ((sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1)) * G / lower) := by
-- proof
  apply StatMech.FrontierD.abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_of_lipschitz hc hN hcharge hopen hsol hlower hdensity x htauLip htauPeriodic htauBound


-- created on 2026-10-23
