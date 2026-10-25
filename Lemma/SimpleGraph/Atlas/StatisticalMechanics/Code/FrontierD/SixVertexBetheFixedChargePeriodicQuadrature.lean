import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargePeriodicQuadrature
open Filter Finset StatMech StatMech.FrontierD


/--
[abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargePeriodicQuadrature.lean)
-/
@[path]
private lemma abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_fixedCharge_eq :
-- imply
  ∀ {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N) (hcharge : N = 2 * (n + 1) + 2 * r) {p : Fin (n + 1) -> Real} (hopen : SixVertexOpenRootSimplex p) (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) {lower : Real} (hlower : 0 < lower) (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N (n + 1) p x) {f : Real -> Real} {C : NNReal} {F : Real} (hf : Continuous f) (hlip : LipschitzWith C f) (hperiodic : Function.Periodic f (2 * Real.pi)) (hfBound : forall x, |f x| <= F), |(∑ j, f (p j)) / N - ∫ y in -Real.pi..Real.pi, f y * sixVertexFiniteRootDensity c N (n + 1) p y| <= (C : Real) * sixVertexFiniteRootDensityUniformBound c * ((2 * (r : Real) + 1) / ((N : Real) * lower)) * (2 * Real.pi) + (2 * (r : Real) / N) * F := by
-- proof
  apply StatMech.FrontierD.abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_fixedCharge


-- created on 2026-10-23
