import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryLayerConsistency.Part3
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[isingFiniteWeighted_harmonic_approximation_of_layer_barriers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma isingFiniteWeighted_harmonic_approximation_of_layer_barriers_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {boundaryError bulkResidual layerResidual bulkBound layerBound : Real}
-- given
  (conductance : V -> V -> Real)
  (boundary layer : V -> Prop)
  (harmonic target bulkBarrier layerBarrier : V -> Real)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (hharmonic : IsingFiniteWeightedHarmonicOn conductance boundary harmonic)
  (hboundary : forall x, boundary x -> |harmonic x - target x| <= boundaryError)
  (hbulkResidual : 0 <= bulkResidual)
  (hlayerResidual : 0 <= layerResidual)
  (hbulk_nonneg : forall x, 0 <= bulkBarrier x)
  (hlayer_nonneg : forall x, 0 <= layerBarrier x)
  (hbulk_bound : forall x, bulkBarrier x <= bulkBound)
  (hlayer_bound : forall x, layerBarrier x <= layerBound)
  (hbulk_laplacian : forall x, Not (boundary x) -> isingFiniteWeightedLaplacian conductance bulkBarrier x <= -1)
  (hlayer_laplacian_nonpos : forall x, Not (boundary x) -> isingFiniteWeightedLaplacian conductance layerBarrier x <= 0)
  (hlayer_laplacian : forall x, Not (boundary x) -> layer x -> isingFiniteWeightedLaplacian conductance layerBarrier x <= -1)
  (htarget_bulk : forall x, Not (boundary x) -> Not (layer x) -> |isingFiniteWeightedLaplacian conductance target x| <= bulkResidual)
  (htarget_layer : forall x, Not (boundary x) -> layer x -> |isingFiniteWeightedLaplacian conductance target x| <= layerResidual) :
-- imply
  forall x, := by
-- proof
  apply StatMech.Universality.isingFiniteWeighted_harmonic_approximation_of_layer_barriers G conductance boundary layer harmonic target bulkBarrier layerBarrier boundaryError bulkResidual layerResidual bulkBound layerBound hconductance hpositive hhit hharmonic hboundary hbulkResidual hlayerResidual hbulk_nonneg hlayer_nonneg hbulk_bound hlayer_bound hbulk_laplacian hlayer_laplacian_nonpos hlayer_laplacian htarget_bulk htarget_layer

/--
[vertexGhostLayerBarrier_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma vertexGhostLayerBarrier_nonneg_eq
  {n : Nat} :
-- imply
  forall x, 0 <= vertexGhostLayerBarrier n x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexGhostLayerBarrier_nonneg n

/--
[faceGhostLayerBarrier_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma faceGhostLayerBarrier_nonneg_eq
  {n : Nat} :
-- imply
  forall c, 0 <= faceGhostLayerBarrier n c := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceGhostLayerBarrier_nonneg n

/--
[vertexGhostLayerBarrier_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma vertexGhostLayerBarrier_le_eq
  {n : Nat} :
-- imply
  forall x, vertexGhostLayerBarrier n x <= 1 / isingFermionicGhostCoefficient := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexGhostLayerBarrier_le n

/--
[faceGhostLayerBarrier_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma faceGhostLayerBarrier_le_eq
  {n : Nat} :
-- imply
  forall c, faceGhostLayerBarrier n c <= 1 / isingFermionicGhostCoefficient := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceGhostLayerBarrier_le n

/--
[vertexGhostLayerBarrier_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma vertexGhostLayerBarrier_laplacian_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexGhostLayerBarrier n) (some x) = -(fkIsingSquareFullVertexGhostMultiplicity n x : Real) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexGhostLayerBarrier_laplacian n x

/--
[faceGhostLayerBarrier_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma faceGhostLayerBarrier_laplacian_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n} :
-- imply
  isingFiniteWeightedLaplacian (faceGhostConductance n) (faceGhostLayerBarrier n) (some c) = -(fkIsingSquareFullFaceGhostMultiplicity n c : Real) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceGhostLayerBarrier_laplacian n c

/--
[vertexGhostLayerBarrier_laplacian_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma vertexGhostLayerBarrier_laplacian_nonpos_eq
  {n : Nat}
  {z : Option (FKIsingSquareFullVertexNode n)}
-- given
  (hz : Not (vertexDirichletBoundary n z)) :
-- imply
  isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexGhostLayerBarrier n) z <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexGhostLayerBarrier_laplacian_nonpos n z hz

/--
[faceGhostLayerBarrier_laplacian_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma faceGhostLayerBarrier_laplacian_nonpos_eq
  {n : Nat}
  {z : Option (FKIsingSquareFullFaceNode n)}
-- given
  (hz : Not (faceDirichletBoundary n z)) :
-- imply
  isingFiniteWeightedLaplacian (faceGhostConductance n) (faceGhostLayerBarrier n) z <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceGhostLayerBarrier_laplacian_nonpos n z hz

/--
[vertexGhostLayerBarrier_laplacian_le_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma vertexGhostLayerBarrier_laplacian_le_neg_one_eq
  {n : Nat}
  {z : Option (FKIsingSquareFullVertexNode n)}
-- given
  (hz : Not (vertexDirichletBoundary n z))
  (hlayer : vertexGhostLayer n z) :
-- imply
  isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexGhostLayerBarrier n) z <= -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexGhostLayerBarrier_laplacian_le_neg_one n z hz hlayer

/--
[faceGhostLayerBarrier_laplacian_le_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma faceGhostLayerBarrier_laplacian_le_neg_one_eq
  {n : Nat}
  {z : Option (FKIsingSquareFullFaceNode n)}
-- given
  (hz : Not (faceDirichletBoundary n z))
  (hlayer : faceGhostLayer n z) :
-- imply
  isingFiniteWeightedLaplacian (faceGhostConductance n) (faceGhostLayerBarrier n) z <= -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceGhostLayerBarrier_laplacian_le_neg_one n z hz hlayer

/--
[vertexDirichlet_target_error_le_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma vertexDirichlet_target_error_le_split_eq
  {n : Nat}
  {bulkResidual layerResidual : Real}
-- given
  (hn : 0 < n)
  (target : Option (FKIsingSquareFullVertexNode n) -> Real)
  (hbulkResidual : 0 <= bulkResidual)
  (hlayerResidual : 0 <= layerResidual)
  (hbulk : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> fkIsingSquareFullVertexGhostMultiplicity n x = 0 -> |isingFiniteWeightedLaplacian (vertexGhostConductance n) target (some x)| <= bulkResidual)
  (hlayer : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity n x -> |isingFiniteWeightedLaplacian (vertexGhostConductance n) target (some x)| <= layerResidual) :
-- imply
  forall z, := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexDirichlet_target_error_le_split n hn target bulkResidual layerResidual hbulkResidual hlayerResidual hbulk hlayer

/--
[faceDirichlet_target_error_le_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma faceDirichlet_target_error_le_split_eq
  {n : Nat}
  {bulkResidual layerResidual : Real}
-- given
  (hn : 0 < n)
  (target : Option (FKIsingSquareFullFaceNode n) -> Real)
  (hbulkResidual : 0 <= bulkResidual)
  (hlayerResidual : 0 <= layerResidual)
  (hbulk : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> fkIsingSquareFullFaceGhostMultiplicity n c = 0 -> |isingFiniteWeightedLaplacian (faceGhostConductance n) target (some c)| <= bulkResidual)
  (hlayer : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity n c -> |isingFiniteWeightedLaplacian (faceGhostConductance n) target (some c)| <= layerResidual) :
-- imply
  forall z, := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceDirichlet_target_error_le_split n hn target bulkResidual layerResidual hbulkResidual hlayerResidual hbulk hlayer

/--
[vertexSampled_target_error_le_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma vertexSampled_target_error_le_split_eq
  {n : Nat}
  {bulkResidual layerResidual : Real}
-- given
  (hn : 0 < n)
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex)
  (hbulkResidual : 0 <= bulkResidual)
  (hlayerResidual : 0 <= layerResidual)
  (hbulk : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> fkIsingSquareFullVertexGhostMultiplicity n x = 0 -> |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => (Phi (embedding y)).im) x| <= bulkResidual)
  (hlayer : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity n x -> |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => (Phi (embedding y)).im) x| <= layerResidual)
  (hfreeTrace : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity n x -> (Phi (embedding x)).im = 1) :
-- imply
  forall z, := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSampled_target_error_le_split n hn embedding Phi bulkResidual layerResidual hbulkResidual hlayerResidual hbulk hlayer hfreeTrace

/--
[faceSampled_target_error_le_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean)
-/
@[path]
private lemma faceSampled_target_error_le_split_eq
  {n : Nat}
  {bulkResidual layerResidual : Real}
-- given
  (hn : 0 < n)
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex)
  (hbulkResidual : 0 <= bulkResidual)
  (hlayerResidual : 0 <= layerResidual)
  (hbulk : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> fkIsingSquareFullFaceGhostMultiplicity n c = 0 -> |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d => (Phi (embedding d)).im) c| <= bulkResidual)
  (hlayer : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity n c -> |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d => (Phi (embedding d)).im) c| <= layerResidual)
  (hfreeTrace : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity n c -> (Phi (embedding c)).im = 0) :
-- imply
  forall z, := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSampled_target_error_le_split n hn embedding Phi bulkResidual layerResidual hbulkResidual hlayerResidual hbulk hlayer hfreeTrace


-- created on 2026-10-23
