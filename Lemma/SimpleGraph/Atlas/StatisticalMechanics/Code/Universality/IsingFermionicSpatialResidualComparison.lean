import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSpatialResidualComparison.Part2
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[vertexSpatialTargetResidual_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean)
-/
@[path]
private lemma vertexSpatialTargetResidual_nonneg_eq
  {n : Nat}
-- given
  (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
-- imply
  forall z, 0 <= vertexSpatialTargetResidual n target z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSpatialTargetResidual_nonneg n target

/--
[vertexSpatialTargetResidualPotential_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean)
-/
@[path]
private lemma vertexSpatialTargetResidualPotential_nonneg_eq
  {n : Nat}
-- given
  (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
-- imply
  forall z, 0 <= vertexSpatialTargetResidualPotential n target z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSpatialTargetResidualPotential_nonneg n target

/--
[vertexSpatialTargetResidualPotential_eq_sum_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean)
-/
@[path]
private lemma vertexSpatialTargetResidualPotential_eq_sum_point_eq
  {n : Nat}
-- given
  (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
-- imply
  vertexSpatialTargetResidualPotential n target = ∑ z ∈ (Finset.univ : Finset (Option (FKIsingSquareFullVertexNode n))), vertexSpatialTargetResidual n target z • vertexPointPoissonBarrier n z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSpatialTargetResidualPotential_eq_sum_point n target

/--
[vertexSpatialTargetResidualPotential_le_sum_point_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean)
-/
@[path]
private lemma vertexSpatialTargetResidualPotential_le_sum_point_bound_eq
  {n : Nat}
  {x : Option (FKIsingSquareFullVertexNode n)}
-- given
  (target : Option (FKIsingSquareFullVertexNode n) -> Real)
  (bound : Option (FKIsingSquareFullVertexNode n) -> Real)
  (hbound : forall z, vertexPointPoissonBarrier n z x <= bound z) :
-- imply
  vertexSpatialTargetResidualPotential n target x <= ∑ z ∈ (Finset.univ : Finset (Option (FKIsingSquareFullVertexNode n))), vertexSpatialTargetResidual n target z * bound z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSpatialTargetResidualPotential_le_sum_point_bound n target x bound hbound

/--
[vertexDirichlet_target_error_le_spatial_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean)
-/
@[path]
private lemma vertexDirichlet_target_error_le_spatial_residual_eq
  {n : Nat}
-- given
  (hn : 0 < n)
  (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
-- imply
  forall z, := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexDirichlet_target_error_le_spatial_residual n hn target

/--
[faceSpatialTargetResidual_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean)
-/
@[path]
private lemma faceSpatialTargetResidual_nonneg_eq
  {n : Nat}
-- given
  (target : Option (FKIsingSquareFullFaceNode n) -> Real) :
-- imply
  forall z, 0 <= faceSpatialTargetResidual n target z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSpatialTargetResidual_nonneg n target

/--
[faceSpatialTargetResidualPotential_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean)
-/
@[path]
private lemma faceSpatialTargetResidualPotential_nonneg_eq
  {n : Nat}
-- given
  (target : Option (FKIsingSquareFullFaceNode n) -> Real) :
-- imply
  forall z, 0 <= faceSpatialTargetResidualPotential n target z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSpatialTargetResidualPotential_nonneg n target

/--
[faceSpatialTargetResidualPotential_eq_sum_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean)
-/
@[path]
private lemma faceSpatialTargetResidualPotential_eq_sum_point_eq
  {n : Nat}
-- given
  (target : Option (FKIsingSquareFullFaceNode n) -> Real) :
-- imply
  faceSpatialTargetResidualPotential n target = ∑ z ∈ (Finset.univ : Finset (Option (FKIsingSquareFullFaceNode n))), faceSpatialTargetResidual n target z • facePointPoissonBarrier n z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSpatialTargetResidualPotential_eq_sum_point n target

/--
[faceSpatialTargetResidualPotential_le_sum_point_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean)
-/
@[path]
private lemma faceSpatialTargetResidualPotential_le_sum_point_bound_eq
  {n : Nat}
  {x : Option (FKIsingSquareFullFaceNode n)}
-- given
  (target : Option (FKIsingSquareFullFaceNode n) -> Real)
  (bound : Option (FKIsingSquareFullFaceNode n) -> Real)
  (hbound : forall z, facePointPoissonBarrier n z x <= bound z) :
-- imply
  faceSpatialTargetResidualPotential n target x <= ∑ z ∈ (Finset.univ : Finset (Option (FKIsingSquareFullFaceNode n))), faceSpatialTargetResidual n target z * bound z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSpatialTargetResidualPotential_le_sum_point_bound n target x bound hbound

/--
[faceDirichlet_target_error_le_spatial_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean)
-/
@[path]
private lemma faceDirichlet_target_error_le_spatial_residual_eq
  {n : Nat}
-- given
  (hn : 0 < n)
  (target : Option (FKIsingSquareFullFaceNode n) -> Real) :
-- imply
  forall z, := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceDirichlet_target_error_le_spatial_residual n hn target

/--
[physicalIncidence_target_error_le_spatial_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean)
-/
@[path]
private lemma physicalIncidence_target_error_le_spatial_residual_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
  {target : Real}
-- given
  (hn : 0 < n)
  (vertexTarget : Option (FKIsingSquareFullVertexNode n) -> Real)
  (faceTarget : Option (FKIsingSquareFullFaceNode n) -> Real)
  (hvertexTarget : vertexTarget (some (fkIsingSquareInteriorRadialEndpoint n hn e)) = target)
  (hfaceTarget : faceTarget (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) = target) :
-- imply
  let vertexError := vertexBoundaryConsistencyError n hn vertexTarget + vertexSpatialTargetResidualPotential n vertexTarget (some (fkIsingSquareInteriorRadialEndpoint n hn e)) let faceError := faceBoundaryConsistencyError n hn faceTarget + faceSpatialTargetResidualPotential n faceTarget (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.physicalIncidence_target_error_le_spatial_residual n hn vertexTarget faceTarget e target hvertexTarget hfaceTarget

/--
[physicalIncidence_uniform_convergence_of_spatial_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean)
-/
@[path]
private lemma physicalIncidence_uniform_convergence_of_spatial_residual_eq
-- given
  (N : Nat -> Nat)
  (hN : forall k, 0 < N k)
  (vertexTarget : forall k, Option (FKIsingSquareFullVertexNode (N k)) -> Real)
  (faceTarget : forall k, Option (FKIsingSquareFullFaceNode (N k)) -> Real)
  (incidenceTarget : forall k, FKIsingSquareInteriorRadialIncidence (N k) (hN k) -> Real)
  (safe : forall k, FKIsingSquareInteriorRadialIncidence (N k) (hN k) -> Prop)
  (rate : Nat -> Real)
  (hvertexTarget : forall k e, vertexTarget k (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) = incidenceTarget k e)
  (hfaceTarget : forall k e, faceTarget k (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) = incidenceTarget k e)
  (hvertexRate : forall k e, safe k e -> vertexBoundaryConsistencyError (N k) (hN k) (vertexTarget k) + vertexSpatialTargetResidualPotential (N k) (vertexTarget k) (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) <= rate k)
  (hfaceRate : forall k e, safe k e -> faceBoundaryConsistencyError (N k) (hN k) (faceTarget k) + faceSpatialTargetResidualPotential (N k) (faceTarget k) (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) <= rate k)
  (hrate : Tendsto rate atTop (nhds 0)) :
-- imply
  forall eta : Real, 0 < eta -> Filter.Eventually (fun k => forall e : FKIsingSquareInteriorRadialIncidence (N k) (hN k), safe k e -> |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) - incidenceTarget k e| < eta /\ |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) - incidenceTarget k e| < eta) atTop := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.physicalIncidence_uniform_convergence_of_spatial_residual N hN vertexTarget faceTarget incidenceTarget safe rate hvertexTarget hfaceTarget hvertexRate hfaceRate hrate


-- created on 2026-10-23
