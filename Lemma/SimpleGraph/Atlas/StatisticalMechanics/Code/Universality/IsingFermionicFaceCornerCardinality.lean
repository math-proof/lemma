import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerCardinality
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[faceMarkedEndpointCode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerCardinality.lean)
-/
@[path]
private lemma faceMarkedEndpointCode_injective_eq
  {n radius : Nat}
  {z w : Option (FKIsingSquareFullFaceNode n)}
-- given
  (hz : faceMarkedEndpointLayer n radius z)
  (hw : faceMarkedEndpointLayer n radius w)
  (hcode : faceMarkedEndpointCode n radius z hz = faceMarkedEndpointCode n radius w hw) :
-- imply
  z = w := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointCode_injective n radius hz hw hcode

/--
[faceInteriorExceptionalSources_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerCardinality.lean)
-/
@[path]
private lemma faceInteriorExceptionalSources_card_le_eq
  {n radius : Nat} :
-- imply
  (isingFiniteWeightedInteriorExceptionalSources (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)).card <= 2 * (radius + 1) ^ 2 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceInteriorExceptionalSources_card_le n radius

/--
[faceInteriorExceptionalSources_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerCardinality.lean)
-/
@[path]
private lemma faceInteriorExceptionalSources_mul_le_eq
  {n radius : Nat}
  {B : Real}
-- given
  (hB : 0 <= B) :
-- imply
  ((isingFiniteWeightedInteriorExceptionalSources (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)).card : Real) * B <= (2 * (radius + 1) ^ 2 : Nat) * B := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceInteriorExceptionalSources_mul_le n radius B hB

/--
[faceMarkedEndpointBarrier_le_radiusDistance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerCardinality.lean)
-/
@[path]
private lemma faceMarkedEndpointBarrier_le_radiusDistance_eq
  {n radius : Nat}
  {distance : Real}
  {source : FKIsingSquareFullFaceNode n}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
  (hleft : 0 < source.1.1)
  (hdistance : 0 < distance)
  (hlowerDistance : distance <= (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient + (source.2.1 : Real))
  (hupperDistance : distance <= (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient + (2 * n - 1 - source.2.1 : Nat)) :
-- imply
  faceMarkedEndpointBarrier n radius (some source) <= (2 * (radius + 1) ^ 2 : Nat) * (((radius : Real) + 1 / isingFermionicGhostCoefficient) * (radius : Real) / distance) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointBarrier_le_radiusDistance n radius distance source hfixed hleft hdistance hlowerDistance hupperDistance

/--
[tendsto_faceEndpointPolynomialBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerCardinality.lean)
-/
@[path]
private lemma tendsto_faceEndpointPolynomialBound_eq :
-- imply
  Filter.Tendsto faceEndpointPolynomialBound Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_faceEndpointPolynomialBound

/--
[faceMarkedEndpointBarrier_le_polynomialBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerCardinality.lean)
-/
@[path]
private lemma faceMarkedEndpointBarrier_le_polynomialBound_eq
  {k : Nat}
  {source : FKIsingSquareFullFaceNode ((k + 1) ^ 5)}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary ((k + 1) ^ 5) source))
  (hleft : 0 < source.1.1)
  (hlowerDistance : ((((k + 1) ^ 5 : Nat) : Real) / 2) <= (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient + (source.2.1 : Real))
  (hupperDistance : ((((k + 1) ^ 5 : Nat) : Real) / 2) <= (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient + (2 * ((k + 1) ^ 5) - 1 - source.2.1 : Nat)) :
-- imply
  faceMarkedEndpointBarrier ((k + 1) ^ 5) (k + 1) (some source) <= faceEndpointPolynomialBound k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointBarrier_le_polynomialBound k source hfixed hleft hlowerDistance hupperDistance

/--
[faceMarkedEndpointBarrier_le_polynomialBound_of_halfColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerCardinality.lean)
-/
@[path]
private lemma faceMarkedEndpointBarrier_le_polynomialBound_of_halfColumn_eq
  {k : Nat}
  {source : FKIsingSquareFullFaceNode ((k + 1) ^ 5)}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary ((k + 1) ^ 5) source))
  (hhalf : ((((k + 1) ^ 5 : Nat) : Real) / 2) <= source.1.1) :
-- imply
  faceMarkedEndpointBarrier ((k + 1) ^ 5) (k + 1) (some source) <= faceEndpointPolynomialBound k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointBarrier_le_polynomialBound_of_halfColumn k source hfixed hhalf

/--
[tendsto_four_mul_faceEndpointPolynomialBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerCardinality.lean)
-/
@[path]
private lemma tendsto_four_mul_faceEndpointPolynomialBound_eq :
-- imply
  Filter.Tendsto (fun k => 4 * faceEndpointPolynomialBound k) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_four_mul_faceEndpointPolynomialBound


-- created on 2026-10-23
