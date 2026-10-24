import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetNodalExplicit
open StatMech StatMech.FrontierD


/--
[abs_sixVertexContinuousOffsetFourier_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetNodalExplicit.lean)
-/
@[path]
private lemma abs_sixVertexContinuousOffsetFourier_le_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  |sixVertexContinuousOffsetFourier c hc x| <= sixVertexContinuousOffsetFourierBound c := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexContinuousOffsetFourier_le hc x

/--
[eventually_uniform_evenChargeDensityOffset_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetNodalExplicit.lean)
-/
@[path]
private lemma eventually_uniform_evenChargeDensityOffset_fourier_eq
  {c : Real}
  {s : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hepsilon : 0 < epsilon) :
-- imply
  ∀ᶠ k : Nat in atTop, ∀ i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k), |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k i) * sixVertexEvenChargeBetheOffset hc s k i - (2 * s : Real) * sixVertexContinuousOffsetFourier c hc (sixVertexFixedChargeBetheRoots hc (2 * s) k i)| < epsilon := by
-- proof
  apply StatMech.FrontierD.eventually_uniform_evenChargeDensityOffset_fourier hc htail s hepsilon

/--
[eventually_uniform_oddChargeDensityOffset_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetNodalExplicit.lean)
-/
@[path]
private lemma eventually_uniform_oddChargeDensityOffset_fourier_eq
  {c : Real}
  {s : Nat}
  {epsilon : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hepsilon : 0 < epsilon) :
-- imply
  ∀ᶠ k : Nat in atTop, ∀ i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k), |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i) * sixVertexOddChargeBetheOffset hc s k i - (2 * s + 1 : Real) * sixVertexContinuousOffsetFourier c hc (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i)| < epsilon := by
-- proof
  apply StatMech.FrontierD.eventually_uniform_oddChargeDensityOffset_fourier hc htail s hepsilon


-- created on 2026-10-23
