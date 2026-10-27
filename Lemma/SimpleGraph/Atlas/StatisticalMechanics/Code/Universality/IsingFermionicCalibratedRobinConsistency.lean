import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCalibratedRobinConsistency
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[vertexCalibratedRobinEmbedding_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCalibratedRobinConsistency.lean)
-/
@[path]
private lemma vertexCalibratedRobinEmbedding_im_eq
  {n : Nat}
  {scale : Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n) :
-- imply
  (vertexCalibratedRobinEmbedding n hn scale x).im = vertexDirichlet n hn (some x) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexCalibratedRobinEmbedding_im n hn scale x

/--
[faceCalibratedRobinEmbedding_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCalibratedRobinConsistency.lean)
-/
@[path]
private lemma faceCalibratedRobinEmbedding_im_eq
  {n : Nat}
  {scale : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n) :
-- imply
  (faceCalibratedRobinEmbedding n hn scale c).im = faceDirichlet n hn (some c) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceCalibratedRobinEmbedding_im n hn scale c

/--
[vertexSampledImaginaryTarget_calibrated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCalibratedRobinConsistency.lean)
-/
@[path]
private lemma vertexSampledImaginaryTarget_calibrated_eq
  {n : Nat}
  {scale : Real}
-- given
  (hn : 0 < n) :
-- imply
  vertexSampledImaginaryTarget n (vertexCalibratedRobinEmbedding n hn scale) id = vertexDirichlet n hn := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSampledImaginaryTarget_calibrated n hn scale

/--
[faceSampledImaginaryTarget_calibrated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCalibratedRobinConsistency.lean)
-/
@[path]
private lemma faceSampledImaginaryTarget_calibrated_eq
  {n : Nat}
  {scale : Real}
-- given
  (hn : 0 < n) :
-- imply
  faceSampledImaginaryTarget n (faceCalibratedRobinEmbedding n hn scale) id = faceDirichlet n hn := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSampledImaginaryTarget_calibrated n hn scale

/--
[vertexCalibratedRobin_boundaryConsistencyError_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCalibratedRobinConsistency.lean)
-/
@[path]
private lemma vertexCalibratedRobin_boundaryConsistencyError_eq_zero_eq
  {n : Nat}
  {scale : Real}
-- given
  (hn : 0 < n) :
-- imply
  vertexBoundaryConsistencyError n hn (vertexSampledImaginaryTarget n (vertexCalibratedRobinEmbedding n hn scale) id) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexCalibratedRobin_boundaryConsistencyError_eq_zero n hn scale

/--
[faceCalibratedRobin_boundaryConsistencyError_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCalibratedRobinConsistency.lean)
-/
@[path]
private lemma faceCalibratedRobin_boundaryConsistencyError_eq_zero_eq
  {n : Nat}
  {scale : Real}
-- given
  (hn : 0 < n) :
-- imply
  faceBoundaryConsistencyError n hn (faceSampledImaginaryTarget n (faceCalibratedRobinEmbedding n hn scale) id) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceCalibratedRobin_boundaryConsistencyError_eq_zero n hn scale

/--
[vertexCalibratedRobin_targetResidual_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCalibratedRobinConsistency.lean)
-/
@[path]
private lemma vertexCalibratedRobin_targetResidual_eq_zero_eq
  {n : Nat}
  {scale : Real}
-- given
  (hn : 0 < n) :
-- imply
  vertexTargetResidual n (vertexSampledImaginaryTarget n (vertexCalibratedRobinEmbedding n hn scale) id) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexCalibratedRobin_targetResidual_eq_zero n hn scale

/--
[faceCalibratedRobin_targetResidual_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCalibratedRobinConsistency.lean)
-/
@[path]
private lemma faceCalibratedRobin_targetResidual_eq_zero_eq
  {n : Nat}
  {scale : Real}
-- given
  (hn : 0 < n) :
-- imply
  faceTargetResidual n (faceSampledImaginaryTarget n (faceCalibratedRobinEmbedding n hn scale) id) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceCalibratedRobin_targetResidual_eq_zero n hn scale

/--
[vertexCalibratedRobin_targetConsistencyError_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCalibratedRobinConsistency.lean)
-/
@[path]
private lemma vertexCalibratedRobin_targetConsistencyError_eq_zero_eq
  {n : Nat}
  {scale : Real}
-- given
  (hn : 0 < n) :
-- imply
  vertexTargetConsistencyError n hn (vertexSampledImaginaryTarget n (vertexCalibratedRobinEmbedding n hn scale) id) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexCalibratedRobin_targetConsistencyError_eq_zero n hn scale

/--
[faceCalibratedRobin_targetConsistencyError_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCalibratedRobinConsistency.lean)
-/
@[path]
private lemma faceCalibratedRobin_targetConsistencyError_eq_zero_eq
  {n : Nat}
  {scale : Real}
-- given
  (hn : 0 < n) :
-- imply
  faceTargetConsistencyError n hn (faceSampledImaginaryTarget n (faceCalibratedRobinEmbedding n hn scale) id) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceCalibratedRobin_targetConsistencyError_eq_zero n hn scale


-- created on 2026-10-23
