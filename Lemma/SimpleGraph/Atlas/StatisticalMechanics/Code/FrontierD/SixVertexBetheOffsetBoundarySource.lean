import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetBoundarySource
open StatMech StatMech.FrontierD


/--
[sixVertexEvenChargeOffsetBoundarySource_eq_boundarySums](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetBoundarySource.lean)
-/
@[path]
private lemma sixVertexEvenChargeOffsetBoundarySource_eq_boundarySums_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexEvenChargeOffsetBoundarySource hc s k j = (∑ i : Fin s, sixVertexTheta c (sixVertexEvenChargeAlignedHalfRoots hc s k j) (sixVertexHalfFilledBetheRoots hc (2 * s + k) (sixVertexEvenChargeLeftBoundaryIndex s k i))) + ∑ i : Fin s, sixVertexTheta c (sixVertexEvenChargeAlignedHalfRoots hc s k j) (sixVertexHalfFilledBetheRoots hc (2 * s + k) (sixVertexEvenChargeRightBoundaryIndex s k i)) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenChargeOffsetBoundarySource_eq_boundarySums hc s k j


-- created on 2026-10-23
