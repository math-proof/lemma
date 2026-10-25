import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointClampedTarget.Part3
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[isingFiniteGraphLaplacian_eq_of_eq_on_neighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma isingFiniteGraphLaplacian_eq_of_eq_on_neighbors_eq
  [Fintype V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (f g : V -> Real)
  (hx : f x = g x)
  (hneighbor : forall y, G.Adj x y -> f y = g y) :
-- imply
  isingFiniteGraphLaplacian G f x = isingFiniteGraphLaplacian G g x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFiniteGraphLaplacian_eq_of_eq_on_neighbors G f g x hx hneighbor

/--
[vertexMarkedEndpointClampedSampledTarget_of_not_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma vertexMarkedEndpointClampedSampledTarget_of_not_fixed_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex)
  (hx : Not (fkIsingSquareFullVertexFixedBoundary n x)) :
-- imply
  vertexMarkedEndpointClampedSampledTarget n embedding Phi (some x) = (Phi (embedding x)).im := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointClampedSampledTarget_of_not_fixed n embedding Phi x hx

/--
[faceMarkedEndpointClampedSampledTarget_of_not_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma faceMarkedEndpointClampedSampledTarget_of_not_fixed_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex)
  (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
-- imply
  faceMarkedEndpointClampedSampledTarget n embedding Phi (some c) = (Phi (embedding c)).im := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointClampedSampledTarget_of_not_fixed n embedding Phi c hc

/--
[vertexMarkedEndpointClamped_boundaryConsistencyError_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma vertexMarkedEndpointClamped_boundaryConsistencyError_le_eq
  {n : Nat}
  {traceBound : Real}
-- given
  (hn : 0 < n)
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex)
  (htrace_nonneg : 0 <= traceBound)
  (htrace : forall x, fkIsingSquareFullVertexFixedBoundary n x -> Not (0 < fkIsingSquareFullVertexGhostMultiplicity n x) -> |0 - (Phi (embedding x)).im| <= traceBound) :
-- imply
  vertexBoundaryConsistencyError n hn (vertexMarkedEndpointClampedSampledTarget n embedding Phi) <= traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointClamped_boundaryConsistencyError_le n hn embedding Phi traceBound htrace_nonneg htrace

/--
[faceMarkedEndpointClamped_boundaryConsistencyError_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma faceMarkedEndpointClamped_boundaryConsistencyError_le_eq
  {n : Nat}
  {traceBound : Real}
-- given
  (hn : 0 < n)
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex)
  (htrace_nonneg : 0 <= traceBound)
  (htrace : forall c, fkIsingSquareFullFaceFixedBoundary n c -> Not (0 < fkIsingSquareFullFaceGhostMultiplicity n c) -> |1 - (Phi (embedding c)).im| <= traceBound) :
-- imply
  faceBoundaryConsistencyError n hn (faceMarkedEndpointClampedSampledTarget n embedding Phi) <= traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointClamped_boundaryConsistencyError_le n hn embedding Phi traceBound htrace_nonneg htrace

/--
[vertexMarkedEndpointClamped_weightedLaplacian_eq_sampled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma vertexMarkedEndpointClamped_weightedLaplacian_eq_sampled_eq
  {n radius : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hradius : 0 < radius)
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex)
  (hx : Not (fkIsingSquareFullVertexFixedBoundary n x))
  (hendpoint : Not (vertexMarkedEndpointLayer n radius (some x))) :
-- imply
  isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexMarkedEndpointClampedSampledTarget n embedding Phi) (some x) = isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexSampledImaginaryTarget n embedding Phi) (some x) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointClamped_weightedLaplacian_eq_sampled n radius hradius embedding Phi x hx hendpoint

/--
[faceMarkedEndpointClamped_weightedLaplacian_eq_sampled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma faceMarkedEndpointClamped_weightedLaplacian_eq_sampled_eq
  {n radius : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hradius : 2 <= radius)
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex)
  (hc : Not (fkIsingSquareFullFaceFixedBoundary n c))
  (hendpoint : Not (faceMarkedEndpointLayer n radius (some c))) :
-- imply
  isingFiniteWeightedLaplacian (faceGhostConductance n) (faceMarkedEndpointClampedSampledTarget n embedding Phi) (some c) = isingFiniteWeightedLaplacian (faceGhostConductance n) (faceSampledImaginaryTarget n embedding Phi) (some c) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointClamped_weightedLaplacian_eq_sampled n radius hradius embedding Phi c hc hendpoint

/--
[vertexMarkedEndpointClamped_weightedLaplacian_le_of_unitRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma vertexMarkedEndpointClamped_weightedLaplacian_le_of_unitRange_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex)
  (hrange : forall x, 0 <= (Phi (embedding x)).im /\ (Phi (embedding x)).im <= 1) :
-- imply
  |isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexMarkedEndpointClampedSampledTarget n embedding Phi) (some x)| <= 4 + 3 * isingFermionicGhostCoefficient := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointClamped_weightedLaplacian_le_of_unitRange n embedding Phi hrange x

/--
[faceMarkedEndpointClamped_weightedLaplacian_le_of_unitRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma faceMarkedEndpointClamped_weightedLaplacian_le_of_unitRange_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex)
  (hrange : forall c, 0 <= (Phi (embedding c)).im /\ (Phi (embedding c)).im <= 1) :
-- imply
  |isingFiniteWeightedLaplacian (faceGhostConductance n) (faceMarkedEndpointClampedSampledTarget n embedding Phi) (some c)| <= 4 + 3 * isingFermionicGhostCoefficient := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointClamped_weightedLaplacian_le_of_unitRange n embedding Phi hrange c

/--
[vertexMarkedEndpointClamped_target_error_le_endpointLocalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma vertexMarkedEndpointClamped_target_error_le_endpointLocalized_eq
  {n : Nat}
  {radius : Nat}
  {traceBound bulkResidual layerResidual endpointResidual : Real}
-- given
  (hn : 0 < n)
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex)
  (htraceBound : 0 <= traceBound)
  (hbulkResidual : 0 <= bulkResidual)
  (hlayerResidual : 0 <= layerResidual)
  (hendpointResidual : 0 <= endpointResidual)
  (htrace : forall x, fkIsingSquareFullVertexFixedBoundary n x -> Not (0 < fkIsingSquareFullVertexGhostMultiplicity n x) -> |0 - (Phi (embedding x)).im| <= traceBound)
  (hbulk : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> fkIsingSquareFullVertexGhostMultiplicity n x = 0 -> Not (vertexMarkedEndpointLayer n radius (some x)) -> |isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexMarkedEndpointClampedSampledTarget n embedding Phi) (some x)| <= bulkResidual)
  (hlayer : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity n x -> Not (vertexMarkedEndpointLayer n radius (some x)) -> |isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexMarkedEndpointClampedSampledTarget n embedding Phi) (some x)| <= layerResidual)
  (hendpoint : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> vertexMarkedEndpointLayer n radius (some x) -> |isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexMarkedEndpointClampedSampledTarget n embedding Phi) (some x)| <= endpointResidual) :
-- imply
  forall z, |vertexDirichlet n hn z - vertexMarkedEndpointClampedSampledTarget n embedding Phi z| <= traceBound + bulkResidual * vertexExplicitPoissonBarrier n z + layerResidual * vertexGhostLayerBarrier n z + endpointResidual * vertexMarkedEndpointBarrier n radius z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointClamped_target_error_le_endpointLocalized n hn radius embedding Phi traceBound bulkResidual layerResidual endpointResidual htraceBound hbulkResidual hlayerResidual hendpointResidual htrace hbulk hlayer hendpoint

/--
[faceMarkedEndpointClamped_target_error_le_endpointLocalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma faceMarkedEndpointClamped_target_error_le_endpointLocalized_eq
  {n : Nat}
  {radius : Nat}
  {traceBound bulkResidual layerResidual endpointResidual : Real}
-- given
  (hn : 0 < n)
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex)
  (htraceBound : 0 <= traceBound)
  (hbulkResidual : 0 <= bulkResidual)
  (hlayerResidual : 0 <= layerResidual)
  (hendpointResidual : 0 <= endpointResidual)
  (htrace : forall c, fkIsingSquareFullFaceFixedBoundary n c -> Not (0 < fkIsingSquareFullFaceGhostMultiplicity n c) -> |1 - (Phi (embedding c)).im| <= traceBound)
  (hbulk : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> fkIsingSquareFullFaceGhostMultiplicity n c = 0 -> Not (faceMarkedEndpointLayer n radius (some c)) -> |isingFiniteWeightedLaplacian (faceGhostConductance n) (faceMarkedEndpointClampedSampledTarget n embedding Phi) (some c)| <= bulkResidual)
  (hlayer : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity n c -> Not (faceMarkedEndpointLayer n radius (some c)) -> |isingFiniteWeightedLaplacian (faceGhostConductance n) (faceMarkedEndpointClampedSampledTarget n embedding Phi) (some c)| <= layerResidual)
  (hendpoint : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> faceMarkedEndpointLayer n radius (some c) -> |isingFiniteWeightedLaplacian (faceGhostConductance n) (faceMarkedEndpointClampedSampledTarget n embedding Phi) (some c)| <= endpointResidual) :
-- imply
  forall z, |faceDirichlet n hn z - faceMarkedEndpointClampedSampledTarget n embedding Phi z| <= traceBound + bulkResidual * faceExplicitPoissonBarrier n z + layerResidual * faceGhostLayerBarrier n z + endpointResidual * faceMarkedEndpointBarrier n radius z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointClamped_target_error_le_endpointLocalized n hn radius embedding Phi traceBound bulkResidual layerResidual endpointResidual htraceBound hbulkResidual hlayerResidual hendpointResidual htrace hbulk hlayer hendpoint

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofSampledResiduals](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma ofSampledResiduals_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {boundaryRate bulkRate layerRate endpointRate : Nat -> Real}
-- given
  (hvertexRadius : forall k, 0 < radius k)
  (hfaceRadius : forall k, 2 <= radius k)
  (hboundary_nonneg : forall k, 0 <= boundaryRate k)
  (hbulk_nonneg : forall k, 0 <= bulkRate k)
  (hlayer_nonneg : forall k, 0 <= layerRate k)
  (hendpoint_nonneg : forall k, 0 <= endpointRate k)
  (hvertexTrace : forall k x, fkIsingSquareFullVertexFixedBoundary (N k) x -> Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) -> |0 - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <= boundaryRate k)
  (hfaceTrace : forall k c, fkIsingSquareFullFaceFixedBoundary (N k) c -> Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) -> |1 - (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| <= boundaryRate k)
  (hvertexBulk : forall k x, Not (fkIsingSquareFullVertexFixedBoundary (N k) x) -> fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 -> Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) -> |isingFiniteWeightedLaplacian (vertexGhostConductance (N k)) (vertexSampledImaginaryTarget (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi) (some x)| <= bulkRate k)
  (hfaceBulk : forall k c, Not (fkIsingSquareFullFaceFixedBoundary (N k) c) -> fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 -> Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) -> |isingFiniteWeightedLaplacian (faceGhostConductance (N k)) (faceSampledImaginaryTarget (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi) (some c)| <= bulkRate k)
  (hvertexLayer : forall k x, Not (fkIsingSquareFullVertexFixedBoundary (N k) x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x -> Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) -> |isingFiniteWeightedLaplacian (vertexGhostConductance (N k)) (vertexSampledImaginaryTarget (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi) (some x)| <= layerRate k)
  (hfaceLayer : forall k c, Not (fkIsingSquareFullFaceFixedBoundary (N k) c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c -> Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) -> |isingFiniteWeightedLaplacian (faceGhostConductance (N k)) (faceSampledImaginaryTarget (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi) (some c)| <= layerRate k)
  (hvertexEndpoint : forall k x, Not (fkIsingSquareFullVertexFixedBoundary (N k) x) -> vertexMarkedEndpointLayer (N k) (radius k) (some x) -> |isingFiniteWeightedLaplacian (vertexGhostConductance (N k)) (vertexMarkedEndpointClampedSampledTarget (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi) (some x)| <= endpointRate k)
  (hfaceEndpoint : forall k c, Not (fkIsingSquareFullFaceFixedBoundary (N k) c) -> faceMarkedEndpointLayer (N k) (radius k) (some c) -> |isingFiniteWeightedLaplacian (faceGhostConductance (N k)) (faceMarkedEndpointClampedSampledTarget (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi) (some c)| <= endpointRate k)
  (hboundary_tendsto : Tendsto boundaryRate atTop (nhds 0))
  (hscaledBulk_tendsto : Tendsto (fun k => bulkRate k * (N k : Real) ^ 2) atTop (nhds 0))
  (hlayer_tendsto : Tendsto layerRate atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius boundaryRate bulkRate layerRate endpointRate := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofSampledResiduals hvertexRadius hfaceRadius hboundary_nonneg hbulk_nonneg hlayer_nonneg hendpoint_nonneg hvertexTrace hfaceTrace hvertexBulk hfaceBulk hvertexLayer hfaceLayer hvertexEndpoint hfaceEndpoint hboundary_tendsto hscaledBulk_tendsto hlayer_tendsto

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.vertex_error_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma vertex_error_le_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {boundaryRate bulkRate layerRate endpointRate : Nat -> Real}
  {H : PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius boundaryRate bulkRate layerRate endpointRate}
  {k : Nat}
  {x : FKIsingSquareFullVertexNode (N k)}
-- given
  (hx : Not (fkIsingSquareFullVertexFixedBoundary (N k) x)) :
-- imply
  |vertexDirichlet (N k) (hN k) (some x) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <= boundaryRate k + bulkRate k * vertexExplicitPoissonBarrier (N k) (some x) + layerRate k * vertexGhostLayerBarrier (N k) (some x) + endpointRate k * vertexMarkedEndpointBarrier (N k) (radius k) (some x) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.vertex_error_le H k x hx

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.face_error_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma face_error_le_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {boundaryRate bulkRate layerRate endpointRate : Nat -> Real}
  {H : PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius boundaryRate bulkRate layerRate endpointRate}
  {k : Nat}
  {c : FKIsingSquareFullFaceNode (N k)}
-- given
  (hc : Not (fkIsingSquareFullFaceFixedBoundary (N k) c)) :
-- imply
  |faceDirichlet (N k) (hN k) (some c) - (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| <= boundaryRate k + bulkRate k * faceExplicitPoissonBarrier (N k) (some c) + layerRate k * faceGhostLayerBarrier (N k) (some c) + endpointRate k * faceMarkedEndpointBarrier (N k) (radius k) (some c) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.face_error_le H k c hc

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma primitive_convergence_away_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {boundaryRate bulkRate layerRate endpointRate : Nat -> Real}
  {H : PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius boundaryRate bulkRate layerRate endpointRate}
-- given
  (safe : forall k, FKIsingSquareInteriorRadialIncidence (N k) (hN k) -> Prop)
  (vertexEndpointWeight faceEndpointWeight mismatchRate : Nat -> Real)
  (hvertexWeight_nonneg : forall k, 0 <= vertexEndpointWeight k)
  (hfaceWeight_nonneg : forall k, 0 <= faceEndpointWeight k)
  (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
  (hsafeVertex : forall k e, safe k e -> Not (fkIsingSquareFullVertexFixedBoundary (N k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)))
  (hsafeFace : forall k e, safe k e -> Not (fkIsingSquareFullFaceFixedBoundary (N k) (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)))
  (hvertexWeight : forall k e, safe k e -> vertexMarkedEndpointBarrier (N k) (radius k) (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) <= vertexEndpointWeight k)
  (hfaceWeight : forall k e, safe k e -> faceMarkedEndpointBarrier (N k) (radius k) (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) <= faceEndpointWeight k)
  (hmismatch : forall k e, safe k e -> |(Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| <= mismatchRate k)
  (hvertexEndpoint_tendsto : Tendsto (fun k => endpointRate k * vertexEndpointWeight k) atTop (nhds 0))
  (hfaceEndpoint_tendsto : Tendsto (fun k => endpointRate k * faceEndpointWeight k) atTop (nhds 0))
  (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
-- imply
  forall eta : Real, 0 < eta -> ∀ᶠ k in atTop, forall e : FKIsingSquareInteriorRadialIncidence (N k) (hN k), safe k e -> |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta /\ |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away H safe vertexEndpointWeight faceEndpointWeight mismatchRate hvertexWeight_nonneg hfaceWeight_nonneg hmismatch_nonneg hsafeVertex hsafeFace hvertexWeight hfaceWeight hmismatch hvertexEndpoint_tendsto hfaceEndpoint_tendsto hmismatch_tendsto

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean)
-/
@[path]
private lemma primitive_convergence_away_polynomial_eq
  {Phi : Complex -> Complex}
  {mesh boundaryRate bulkRate layerRate : Nat -> Real}
-- given
  (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicPolynomialSide isingFermionicPolynomialSide_pos Phi mesh isingFermionicPolynomialRadius boundaryRate bulkRate layerRate (fun _ => 4 + 3 * isingFermionicGhostCoefficient))
  (mismatchRate : Nat -> Real)
  (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
  (hmismatch : forall k e, PhysicalPolynomialEndpointSafe k e -> |(Phi (fullSquareScaledFaceEmbedding (isingFermionicPolynomialSide k) (mesh k) (fkIsingSquareFullFaceOfRadialIncidence (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e))).im - (Phi (fullSquareScaledVertexEmbedding (isingFermionicPolynomialSide k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e))).im| <= mismatchRate k)
  (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
-- imply
  forall eta : Real, 0 < eta -> ∀ᶠ k in atTop, forall e : FKIsingSquareInteriorRadialIncidence (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k), PhysicalPolynomialEndpointSafe k e -> |(fkIsingSquareBoundaryLayerCoordinateOneForm (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e) - (Phi (fullSquareScaledVertexEmbedding (isingFermionicPolynomialSide k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e))).im| < eta /\ |(fkIsingSquareBoundaryLayerCoordinateOneForm (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e) - (Phi (fullSquareScaledVertexEmbedding (isingFermionicPolynomialSide k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e))).im| < eta := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away_polynomial H mismatchRate hmismatch_nonneg hmismatch hmismatch_tendsto


-- created on 2026-10-23
