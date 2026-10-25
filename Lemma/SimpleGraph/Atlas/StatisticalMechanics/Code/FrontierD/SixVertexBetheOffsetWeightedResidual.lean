import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetWeightedResidual
open StatMech StatMech.FrontierD


/--
[sixVertexEvenChargeOffsetNodalResidual_eq_weightedConvolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetWeightedResidual.lean)
-/
@[path]
private lemma sixVertexEvenChargeOffsetNodalResidual_eq_weightedConvolution_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexEvenChargeOffsetNodalResidual hc s k j = 2 * Real.pi * (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k j) * sixVertexEvenChargeBetheOffset hc s k j) - sixVertexEvenChargeOffsetBoundarySource hc s k j + (1 / (sixVertexFourWidth (2 * s) k : Real)) * ∑ l, sixVertexContinuousOffsetKernel c (sixVertexFixedChargeBetheRoots hc (2 * s) k j) (sixVertexFixedChargeBetheRoots hc (2 * s) k l) * sixVertexEvenChargeBetheOffset hc s k l := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenChargeOffsetNodalResidual_eq_weightedConvolution hc s k j

/--
[sixVertexOddChargeOffsetNodalResidual_eq_weightedConvolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetWeightedResidual.lean)
-/
@[path]
private lemma sixVertexOddChargeOffsetNodalResidual_eq_weightedConvolution_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexOddChargeOffsetNodalResidual hc s k j = 2 * Real.pi * (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) * sixVertexOddChargeBetheOffset hc s k j) - sixVertexOddChargeOffsetBoundarySource hc s k j + (1 / (sixVertexFourWidth (2 * s + 1) k : Real)) * ∑ l, sixVertexContinuousOffsetKernel c (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l) * sixVertexOddChargeBetheOffset hc s k l := by
-- proof
  apply StatMech.FrontierD.sixVertexOddChargeOffsetNodalResidual_eq_weightedConvolution hc s k j


-- created on 2026-10-23
