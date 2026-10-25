import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerCardinality.Part2
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[vertexMarkedEndpointCode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerCardinality.lean)
-/
@[path]
private lemma vertexMarkedEndpointCode_injective_eq
  {n radius : Nat}
  {z w : Option (FKIsingSquareFullVertexNode n)}
-- given
  (hz : vertexMarkedEndpointLayer n radius z)
  (hw : vertexMarkedEndpointLayer n radius w)
  (hcode : vertexMarkedEndpointCode n radius z hz = vertexMarkedEndpointCode n radius w hw) :
-- imply
  z = w := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointCode_injective n radius hz hw hcode

/--
[vertexInteriorExceptionalSources_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerCardinality.lean)
-/
@[path]
private lemma vertexInteriorExceptionalSources_card_le_eq
  {n radius : Nat} :
-- imply
  (isingFiniteWeightedInteriorExceptionalSources (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)).card <= 2 * (radius + 1) ^ 2 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexInteriorExceptionalSources_card_le n radius

/--
[vertexInteriorExceptionalSources_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerCardinality.lean)
-/
@[path]
private lemma vertexInteriorExceptionalSources_mul_le_eq
  {n radius : Nat}
  {B : Real}
-- given
  (hB : 0 <= B) :
-- imply
  ((isingFiniteWeightedInteriorExceptionalSources (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)).card : Real) * B <= (2 * (radius + 1) ^ 2 : Nat) * B := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexInteriorExceptionalSources_mul_le n radius B hB

/--
[vertexMarkedEndpointBarrier_le_radiusDistance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerCardinality.lean)
-/
@[path]
private lemma vertexMarkedEndpointBarrier_le_radiusDistance_eq
  {n radius : Nat}
  {distance : Real}
  {source : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
  (hright : source.1 0 < (n : Int))
  (hbottom : -(n : Int) < source.1 1)
  (htop : source.1 1 < (n : Int))
  (hdistance : 0 < distance)
  (hlowerDistance : distance <= (fullVertexColumnIndex n source : Real) + (fullVertexRowIndex n source : Real) + 1 / isingFermionicGhostCoefficient)
  (hupperDistance : distance <= (fullVertexColumnIndex n source : Real) + (2 * n - fullVertexRowIndex n source : Nat) + 1 / isingFermionicGhostCoefficient) :
-- imply
  vertexMarkedEndpointBarrier n radius (some source) <= (2 * (radius + 1) ^ 2 : Nat) * ((radius : Real) * ((radius : Real) + 1 / isingFermionicGhostCoefficient) / distance) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointBarrier_le_radiusDistance n radius distance source hn hfixed hright hbottom htop hdistance hlowerDistance hupperDistance

/--
[tendsto_vertexEndpointPolynomialBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerCardinality.lean)
-/
@[path]
private lemma tendsto_vertexEndpointPolynomialBound_eq :
-- imply
  Filter.Tendsto vertexEndpointPolynomialBound Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_vertexEndpointPolynomialBound

/--
[vertexMarkedEndpointBarrier_le_polynomialBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerCardinality.lean)
-/
@[path]
private lemma vertexMarkedEndpointBarrier_le_polynomialBound_eq
  {k : Nat}
  {source : FKIsingSquareFullVertexNode ((k + 1) ^ 5)}
-- given
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary ((k + 1) ^ 5) source))
  (hright : source.1 0 < (((k + 1) ^ 5 : Nat) : Int))
  (hbottom : -((((k + 1) ^ 5 : Nat) : Int)) < source.1 1)
  (htop : source.1 1 < (((k + 1) ^ 5 : Nat) : Int))
  (hlowerDistance : ((((k + 1) ^ 5 : Nat) : Real) / 2) <= (fullVertexColumnIndex ((k + 1) ^ 5) source : Real) + (fullVertexRowIndex ((k + 1) ^ 5) source : Real) + 1 / isingFermionicGhostCoefficient)
  (hupperDistance : ((((k + 1) ^ 5 : Nat) : Real) / 2) <= (fullVertexColumnIndex ((k + 1) ^ 5) source : Real) + (2 * ((k + 1) ^ 5) - fullVertexRowIndex ((k + 1) ^ 5) source : Nat) + 1 / isingFermionicGhostCoefficient) :
-- imply
  vertexMarkedEndpointBarrier ((k + 1) ^ 5) (k + 1) (some source) <= vertexEndpointPolynomialBound k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointBarrier_le_polynomialBound k source hfixed hright hbottom htop hlowerDistance hupperDistance

/--
[vertexMarkedEndpointBarrier_le_polynomialBound_of_halfColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerCardinality.lean)
-/
@[path]
private lemma vertexMarkedEndpointBarrier_le_polynomialBound_of_halfColumn_eq
  {k : Nat}
  {source : FKIsingSquareFullVertexNode ((k + 1) ^ 5)}
-- given
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary ((k + 1) ^ 5) source))
  (hright : source.1 0 < (((k + 1) ^ 5 : Nat) : Int))
  (hbottom : -((((k + 1) ^ 5 : Nat) : Int)) < source.1 1)
  (htop : source.1 1 < (((k + 1) ^ 5 : Nat) : Int))
  (hhalf : ((((k + 1) ^ 5 : Nat) : Real) / 2) <= fullVertexColumnIndex ((k + 1) ^ 5) source) :
-- imply
  vertexMarkedEndpointBarrier ((k + 1) ^ 5) (k + 1) (some source) <= vertexEndpointPolynomialBound k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointBarrier_le_polynomialBound_of_halfColumn k source hfixed hright hbottom htop hhalf

/--
[tendsto_four_mul_vertexEndpointPolynomialBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerCardinality.lean)
-/
@[path]
private lemma tendsto_four_mul_vertexEndpointPolynomialBound_eq :
-- imply
  Filter.Tendsto (fun k => 4 * vertexEndpointPolynomialBound k) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_four_mul_vertexEndpointPolynomialBound


-- created on 2026-10-23
