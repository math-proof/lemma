import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialPointGreen
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[endpointRadialGreenConstant_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialPointGreen.lean)
-/
@[path]
private lemma endpointRadialGreenConstant_nonneg_eq :
-- imply
  0 <= endpointRadialGreenConstant := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.endpointRadialGreenConstant_nonneg

/--
[vertexPointPoissonBarrier_le_endpointRadial_of_halfColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialPointGreen.lean)
-/
@[path]
private lemma vertexPointPoissonBarrier_le_endpointRadial_of_halfColumn_eq
  {n : Nat}
  {observation : FKIsingSquareFullVertexNode n}
  {z : Option (FKIsingSquareFullVertexNode n)}
-- given
  (hn : 0 < n)
  (hz : Not (vertexDirichletBoundary n z))
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n observation))
  (hright : observation.1 0 < (n : Int))
  (hbottom : -(n : Int) < observation.1 1)
  (htop : observation.1 1 < (n : Int))
  (hhalf : ((n : Real) / 2) <= fullVertexColumnIndex n observation) :
-- imply
  vertexPointPoissonBarrier n z (some observation) <= (vertexEndpointRadialShell n z : Real) * ((vertexEndpointRadialShell n z : Real) + 1 / isingFermionicGhostCoefficient) / ((n : Real) / 2) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexPointPoissonBarrier_le_endpointRadial_of_halfColumn n hn observation z hz hfixed hright hbottom htop hhalf

/--
[facePointPoissonBarrier_le_endpointRadial_of_halfColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialPointGreen.lean)
-/
@[path]
private lemma facePointPoissonBarrier_le_endpointRadial_of_halfColumn_eq
  {n : Nat}
  {observation : FKIsingSquareFullFaceNode n}
  {z : Option (FKIsingSquareFullFaceNode n)}
-- given
  (hn : 0 < n)
  (hz : Not (faceDirichletBoundary n z))
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n observation))
  (hhalf : ((n : Real) / 2) <= observation.1.1) :
-- imply
  facePointPoissonBarrier n z (some observation) <= ((faceEndpointRadialShell n z : Real) + 1 / isingFermionicGhostCoefficient) * (faceEndpointRadialShell n z : Real) / ((n : Real) / 2) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.facePointPoissonBarrier_le_endpointRadial_of_halfColumn n hn observation z hz hfixed hhalf

/--
[vertexPointPoissonBarrier_le_endpointRadialQuadratic_of_halfColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialPointGreen.lean)
-/
@[path]
private lemma vertexPointPoissonBarrier_le_endpointRadialQuadratic_of_halfColumn_eq
  {n : Nat}
  {observation : FKIsingSquareFullVertexNode n}
  {z : Option (FKIsingSquareFullVertexNode n)}
-- given
  (hn : 0 < n)
  (hz : Not (vertexDirichletBoundary n z))
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n observation))
  (hright : observation.1 0 < (n : Int))
  (hbottom : -(n : Int) < observation.1 1)
  (htop : observation.1 1 < (n : Int))
  (hhalf : ((n : Real) / 2) <= fullVertexColumnIndex n observation) :
-- imply
  vertexPointPoissonBarrier n z (some observation) <= endpointRadialGreenConstant * ((vertexEndpointRadialShell n z + 1 : Nat) : Real) ^ 2 / (n : Real) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexPointPoissonBarrier_le_endpointRadialQuadratic_of_halfColumn n hn observation z hz hfixed hright hbottom htop hhalf

/--
[facePointPoissonBarrier_le_endpointRadialQuadratic_of_halfColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialPointGreen.lean)
-/
@[path]
private lemma facePointPoissonBarrier_le_endpointRadialQuadratic_of_halfColumn_eq
  {n : Nat}
  {observation : FKIsingSquareFullFaceNode n}
  {z : Option (FKIsingSquareFullFaceNode n)}
-- given
  (hn : 0 < n)
  (hz : Not (faceDirichletBoundary n z))
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n observation))
  (hhalf : ((n : Real) / 2) <= observation.1.1) :
-- imply
  facePointPoissonBarrier n z (some observation) <= endpointRadialGreenConstant * ((faceEndpointRadialShell n z + 1 : Nat) : Real) ^ 2 / (n : Real) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.facePointPoissonBarrier_le_endpointRadialQuadratic_of_halfColumn n hn observation z hz hfixed hhalf

/--
[vertexSpatialTargetResidualPotential_le_endpointRadialHarmonic_of_residualDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialPointGreen.lean)
-/
@[path]
private lemma vertexSpatialTargetResidualPotential_le_endpointRadialHarmonic_of_residualDecay_eq
  {n : Nat}
  {observation : FKIsingSquareFullVertexNode n}
  {R : Real}
-- given
  (hn : 0 < n)
  (target : Option (FKIsingSquareFullVertexNode n) -> Real)
  (hR : 0 <= R)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n observation))
  (hright : observation.1 0 < (n : Int))
  (hbottom : -(n : Int) < observation.1 1)
  (htop : observation.1 1 < (n : Int))
  (hhalf : ((n : Real) / 2) <= fullVertexColumnIndex n observation)
  (hresidual : forall z, vertexSpatialTargetResidual n target z <= R / (((vertexEndpointRadialShell n z + 1 : Nat) : Real) ^ 4)) :
-- imply
  vertexSpatialTargetResidualPotential n target (some observation) <= (R * endpointRadialGreenConstant) * 3 * (harmonic (3 * n + 1) : Real) / (n : Real) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSpatialTargetResidualPotential_le_endpointRadialHarmonic_of_residualDecay n hn target observation R hR hfixed hright hbottom htop hhalf hresidual

/--
[faceSpatialTargetResidualPotential_le_endpointRadialHarmonic_of_residualDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialPointGreen.lean)
-/
@[path]
private lemma faceSpatialTargetResidualPotential_le_endpointRadialHarmonic_of_residualDecay_eq
  {n : Nat}
  {observation : FKIsingSquareFullFaceNode n}
  {R : Real}
-- given
  (hn : 0 < n)
  (target : Option (FKIsingSquareFullFaceNode n) -> Real)
  (hR : 0 <= R)
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n observation))
  (hhalf : ((n : Real) / 2) <= observation.1.1)
  (hresidual : forall z, faceSpatialTargetResidual n target z <= R / (((faceEndpointRadialShell n z + 1 : Nat) : Real) ^ 4)) :
-- imply
  faceSpatialTargetResidualPotential n target (some observation) <= (R * endpointRadialGreenConstant) * 3 * (harmonic (3 * n + 1) : Real) / (n : Real) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSpatialTargetResidualPotential_le_endpointRadialHarmonic_of_residualDecay n hn target observation R hR hfixed hhalf hresidual


-- created on 2026-10-23
