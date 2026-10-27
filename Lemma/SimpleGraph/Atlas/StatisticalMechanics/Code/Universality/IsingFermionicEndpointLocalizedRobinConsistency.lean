import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency.Part4
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[isingFiniteWeightedLocalizedPoissonBarrier_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma isingFiniteWeightedLocalizedPoissonBarrier_boundary_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (conductance : V -> V -> Real)
  (boundary exceptional : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (hx : boundary x) :
-- imply
  isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary exceptional hconductance hpositive hhit x = 0 := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLocalizedPoissonBarrier_boundary G conductance boundary exceptional hconductance hpositive hhit x hx

/--
[isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (conductance : V -> V -> Real)
  (boundary exceptional : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (hx : Not (boundary x))
  (hxe : exceptional x) :
-- imply
  isingFiniteWeightedLaplacian conductance (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary exceptional hconductance hpositive hhit) x = -1 := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem G conductance boundary exceptional hconductance hpositive hhit x hx hxe

/--
[isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_not_mem_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (conductance : V -> V -> Real)
  (boundary exceptional : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (hx : Not (boundary x))
  (hxe : Not (exceptional x)) :
-- imply
  isingFiniteWeightedLaplacian conductance (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary exceptional hconductance hpositive hhit) x = 0 := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_not_mem G conductance boundary exceptional hconductance hpositive hhit x hx hxe

/--
[isingFiniteWeightedLocalizedPoissonBarrier_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma isingFiniteWeightedLocalizedPoissonBarrier_nonneg_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
-- given
  (conductance : V -> V -> Real)
  (boundary exceptional : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b) :
-- imply
  forall x, 0 <= isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary exceptional hconductance hpositive hhit x := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLocalizedPoissonBarrier_nonneg G conductance boundary exceptional hconductance hpositive hhit

/--
[isingFiniteWeighted_harmonic_approximation_of_endpoint_barriers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma isingFiniteWeighted_harmonic_approximation_of_endpoint_barriers_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {boundaryError bulkResidual layerResidual endpointResidual : Real}
-- given
  (conductance : V -> V -> Real)
  (boundary layer exceptional : V -> Prop)
  (harmonic target bulkBarrier layerBarrier endpointBarrier : V -> Real)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (hharmonic : IsingFiniteWeightedHarmonicOn conductance boundary harmonic)
  (hboundary : forall x, boundary x -> |harmonic x - target x| <= boundaryError)
  (hbulkResidual : 0 <= bulkResidual)
  (hlayerResidual : 0 <= layerResidual)
  (hendpointResidual : 0 <= endpointResidual)
  (hbulk_nonneg : forall x, 0 <= bulkBarrier x)
  (hlayer_nonneg : forall x, 0 <= layerBarrier x)
  (hendpoint_nonneg : forall x, 0 <= endpointBarrier x)
  (hbulk_laplacian : forall x, Not (boundary x) -> isingFiniteWeightedLaplacian conductance bulkBarrier x <= -1)
  (hlayer_laplacian_nonpos : forall x, Not (boundary x) -> isingFiniteWeightedLaplacian conductance layerBarrier x <= 0)
  (hlayer_laplacian : forall x, Not (boundary x) -> layer x -> isingFiniteWeightedLaplacian conductance layerBarrier x <= -1)
  (hendpoint_laplacian_nonpos : forall x, Not (boundary x) -> isingFiniteWeightedLaplacian conductance endpointBarrier x <= 0)
  (hendpoint_laplacian : forall x, Not (boundary x) -> exceptional x -> isingFiniteWeightedLaplacian conductance endpointBarrier x <= -1)
  (htarget_bulk : forall x, Not (boundary x) -> Not (layer x) -> Not (exceptional x) -> |isingFiniteWeightedLaplacian conductance target x| <= bulkResidual)
  (htarget_layer : forall x, Not (boundary x) -> layer x -> Not (exceptional x) -> |isingFiniteWeightedLaplacian conductance target x| <= layerResidual)
  (htarget_endpoint : forall x, Not (boundary x) -> exceptional x -> |isingFiniteWeightedLaplacian conductance target x| <= endpointResidual) :
-- imply
  forall x, |harmonic x - target x| <= boundaryError + bulkResidual * bulkBarrier x + layerResidual * layerBarrier x + endpointResidual * endpointBarrier x := by
-- proof
  apply StatMech.Universality.isingFiniteWeighted_harmonic_approximation_of_endpoint_barriers G conductance boundary layer exceptional harmonic target bulkBarrier layerBarrier endpointBarrier boundaryError bulkResidual layerResidual endpointResidual hconductance hpositive hhit hharmonic hboundary hbulkResidual hlayerResidual hendpointResidual hbulk_nonneg hlayer_nonneg hendpoint_nonneg hbulk_laplacian hlayer_laplacian_nonpos hlayer_laplacian hendpoint_laplacian_nonpos hendpoint_laplacian htarget_bulk htarget_layer htarget_endpoint

/--
[expandingSquare_scaledFourth_factor_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma expandingSquare_scaledFourth_factor_eq_one_eq
  {k : Nat} :
-- imply
  |fkIsingExpandingSquareScale k| ^ 4 * (fkIsingExpandingSquareSide k : Real) ^ 2 = 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.expandingSquare_scaledFourth_factor_eq_one k

/--
[tendsto_expandingSquare_scaledFourth_of_bound_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma tendsto_expandingSquare_scaledFourth_of_bound_tendsto_eq
-- given
  (derivativeBound : Nat -> Real)
  (hbound : Tendsto derivativeBound atTop (nhds 0)) :
-- imply
  Tendsto (fun k => derivativeBound k * |fkIsingExpandingSquareScale k| ^ 4 * (fkIsingExpandingSquareSide k : Real) ^ 2) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_expandingSquare_scaledFourth_of_bound_tendsto derivativeBound hbound

/--
[vertex_fixed_ghost_mem_markedEndpointLayer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma vertex_fixed_ghost_mem_markedEndpointLayer_eq
  {n radius : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hfixed : fkIsingSquareFullVertexFixedBoundary n x)
  (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity n x) :
-- imply
  vertexMarkedEndpointLayer n radius (some x) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_fixed_ghost_mem_markedEndpointLayer n radius x hfixed hghost

/--
[vertex_adj_fixed_ghost_mem_markedEndpointLayer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma vertex_adj_fixed_ghost_mem_markedEndpointLayer_eq
  {n radius : Nat}
  {x y : FKIsingSquareFullVertexNode n}
-- given
  (hradius : 0 < radius)
  (hxy : (fkIsingSquareFullVertexGraph n).Adj x y)
  (hfixed : fkIsingSquareFullVertexFixedBoundary n y)
  (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity n y) :
-- imply
  vertexMarkedEndpointLayer n radius (some x) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertex_adj_fixed_ghost_mem_markedEndpointLayer n radius hradius x y hxy hfixed hghost

/--
[face_fixed_ghost_mem_markedEndpointLayer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma face_fixed_ghost_mem_markedEndpointLayer_eq
  {n radius : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hradius : 0 < radius)
  (hfixed : fkIsingSquareFullFaceFixedBoundary n c)
  (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity n c) :
-- imply
  faceMarkedEndpointLayer n radius (some c) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.face_fixed_ghost_mem_markedEndpointLayer n radius hradius c hfixed hghost

/--
[face_adj_fixed_ghost_mem_markedEndpointLayer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma face_adj_fixed_ghost_mem_markedEndpointLayer_eq
  {n radius : Nat}
  {c d : FKIsingSquareFullFaceNode n}
-- given
  (hradius : 2 <= radius)
  (hcd : (fkIsingSquareFullFaceGraph n).Adj c d)
  (hfixed : fkIsingSquareFullFaceFixedBoundary n d)
  (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity n d) :
-- imply
  faceMarkedEndpointLayer n radius (some c) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.face_adj_fixed_ghost_mem_markedEndpointLayer n radius hradius c d hcd hfixed hghost

/--
[vertexMarkedEndpointBarrier_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma vertexMarkedEndpointBarrier_nonneg_eq
  {n radius : Nat} :
-- imply
  forall z, 0 <= vertexMarkedEndpointBarrier n radius z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointBarrier_nonneg n radius

/--
[faceMarkedEndpointBarrier_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma faceMarkedEndpointBarrier_nonneg_eq
  {n radius : Nat} :
-- imply
  forall z, 0 <= faceMarkedEndpointBarrier n radius z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointBarrier_nonneg n radius

/--
[vertexMarkedEndpointBarrier_laplacian_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma vertexMarkedEndpointBarrier_laplacian_nonpos_eq
  {n radius : Nat}
  {z : Option (FKIsingSquareFullVertexNode n)}
-- given
  (hz : Not (vertexDirichletBoundary n z)) :
-- imply
  isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexMarkedEndpointBarrier n radius) z <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointBarrier_laplacian_nonpos n radius z hz

/--
[faceMarkedEndpointBarrier_laplacian_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma faceMarkedEndpointBarrier_laplacian_nonpos_eq
  {n radius : Nat}
  {z : Option (FKIsingSquareFullFaceNode n)}
-- given
  (hz : Not (faceDirichletBoundary n z)) :
-- imply
  isingFiniteWeightedLaplacian (faceGhostConductance n) (faceMarkedEndpointBarrier n radius) z <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointBarrier_laplacian_nonpos n radius z hz

/--
[vertexMarkedEndpointBarrier_laplacian_le_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma vertexMarkedEndpointBarrier_laplacian_le_neg_one_eq
  {n radius : Nat}
  {z : Option (FKIsingSquareFullVertexNode n)}
-- given
  (hz : Not (vertexDirichletBoundary n z))
  (hze : vertexMarkedEndpointLayer n radius z) :
-- imply
  isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexMarkedEndpointBarrier n radius) z <= -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointBarrier_laplacian_le_neg_one n radius z hz hze

/--
[faceMarkedEndpointBarrier_laplacian_le_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma faceMarkedEndpointBarrier_laplacian_le_neg_one_eq
  {n radius : Nat}
  {z : Option (FKIsingSquareFullFaceNode n)}
-- given
  (hz : Not (faceDirichletBoundary n z))
  (hze : faceMarkedEndpointLayer n radius z) :
-- imply
  isingFiniteWeightedLaplacian (faceGhostConductance n) (faceMarkedEndpointBarrier n radius) z <= -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointBarrier_laplacian_le_neg_one n radius z hz hze

/--
[vertexDirichlet_target_error_le_endpointLocalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma vertexDirichlet_target_error_le_endpointLocalized_eq
  {n : Nat}
  {radius : Nat}
  {bulkResidual layerResidual endpointResidual : Real}
-- given
  (hn : 0 < n)
  (target : Option (FKIsingSquareFullVertexNode n) -> Real)
  (hbulkResidual : 0 <= bulkResidual)
  (hlayerResidual : 0 <= layerResidual)
  (hendpointResidual : 0 <= endpointResidual)
  (hbulk : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> fkIsingSquareFullVertexGhostMultiplicity n x = 0 -> Not (vertexMarkedEndpointLayer n radius (some x)) -> |isingFiniteWeightedLaplacian (vertexGhostConductance n) target (some x)| <= bulkResidual)
  (hlayer : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity n x -> Not (vertexMarkedEndpointLayer n radius (some x)) -> |isingFiniteWeightedLaplacian (vertexGhostConductance n) target (some x)| <= layerResidual)
  (hendpoint : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> vertexMarkedEndpointLayer n radius (some x) -> |isingFiniteWeightedLaplacian (vertexGhostConductance n) target (some x)| <= endpointResidual) :
-- imply
  forall z, |vertexDirichlet n hn z - target z| <= vertexBoundaryConsistencyError n hn target + bulkResidual * vertexExplicitPoissonBarrier n z + layerResidual * vertexGhostLayerBarrier n z + endpointResidual * vertexMarkedEndpointBarrier n radius z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexDirichlet_target_error_le_endpointLocalized n hn radius target bulkResidual layerResidual endpointResidual hbulkResidual hlayerResidual hendpointResidual hbulk hlayer hendpoint

/--
[faceDirichlet_target_error_le_endpointLocalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma faceDirichlet_target_error_le_endpointLocalized_eq
  {n : Nat}
  {radius : Nat}
  {bulkResidual layerResidual endpointResidual : Real}
-- given
  (hn : 0 < n)
  (target : Option (FKIsingSquareFullFaceNode n) -> Real)
  (hbulkResidual : 0 <= bulkResidual)
  (hlayerResidual : 0 <= layerResidual)
  (hendpointResidual : 0 <= endpointResidual)
  (hbulk : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> fkIsingSquareFullFaceGhostMultiplicity n c = 0 -> Not (faceMarkedEndpointLayer n radius (some c)) -> |isingFiniteWeightedLaplacian (faceGhostConductance n) target (some c)| <= bulkResidual)
  (hlayer : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity n c -> Not (faceMarkedEndpointLayer n radius (some c)) -> |isingFiniteWeightedLaplacian (faceGhostConductance n) target (some c)| <= layerResidual)
  (hendpoint : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> faceMarkedEndpointLayer n radius (some c) -> |isingFiniteWeightedLaplacian (faceGhostConductance n) target (some c)| <= endpointResidual) :
-- imply
  forall z, |faceDirichlet n hn z - target z| <= faceBoundaryConsistencyError n hn target + bulkResidual * faceExplicitPoissonBarrier n z + layerResidual * faceGhostLayerBarrier n z + endpointResidual * faceMarkedEndpointBarrier n radius z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceDirichlet_target_error_le_endpointLocalized n hn radius target bulkResidual layerResidual endpointResidual hbulkResidual hlayerResidual hendpointResidual hbulk hlayer hendpoint

/--
[vertexSampled_target_error_le_endpointLocalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma vertexSampled_target_error_le_endpointLocalized_eq
  {n : Nat}
  {radius : Nat}
  {bulkResidual layerResidual endpointResidual : Real}
-- given
  (hn : 0 < n)
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex)
  (hbulkResidual : 0 <= bulkResidual)
  (hlayerResidual : 0 <= layerResidual)
  (hendpointResidual : 0 <= endpointResidual)
  (hbulk : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> fkIsingSquareFullVertexGhostMultiplicity n x = 0 -> Not (vertexMarkedEndpointLayer n radius (some x)) -> |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => (Phi (embedding y)).im) x| <= bulkResidual)
  (hlayer : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity n x -> Not (vertexMarkedEndpointLayer n radius (some x)) -> |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => (Phi (embedding y)).im) x| <= layerResidual)
  (hendpoint : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> vertexMarkedEndpointLayer n radius (some x) -> |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => (Phi (embedding y)).im) x| <= endpointResidual)
  (hfreeTrace : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity n x -> (Phi (embedding x)).im = 1) :
-- imply
  forall z, |vertexDirichlet n hn z - vertexSampledImaginaryTarget n embedding Phi z| <= vertexBoundaryConsistencyError n hn (vertexSampledImaginaryTarget n embedding Phi) + bulkResidual * vertexExplicitPoissonBarrier n z + layerResidual * vertexGhostLayerBarrier n z + endpointResidual * vertexMarkedEndpointBarrier n radius z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSampled_target_error_le_endpointLocalized n hn radius embedding Phi bulkResidual layerResidual endpointResidual hbulkResidual hlayerResidual hendpointResidual hbulk hlayer hendpoint hfreeTrace

/--
[faceSampled_target_error_le_endpointLocalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma faceSampled_target_error_le_endpointLocalized_eq
  {n : Nat}
  {radius : Nat}
  {bulkResidual layerResidual endpointResidual : Real}
-- given
  (hn : 0 < n)
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex)
  (hbulkResidual : 0 <= bulkResidual)
  (hlayerResidual : 0 <= layerResidual)
  (hendpointResidual : 0 <= endpointResidual)
  (hbulk : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> fkIsingSquareFullFaceGhostMultiplicity n c = 0 -> Not (faceMarkedEndpointLayer n radius (some c)) -> |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d => (Phi (embedding d)).im) c| <= bulkResidual)
  (hlayer : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity n c -> Not (faceMarkedEndpointLayer n radius (some c)) -> |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d => (Phi (embedding d)).im) c| <= layerResidual)
  (hendpoint : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> faceMarkedEndpointLayer n radius (some c) -> |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d => (Phi (embedding d)).im) c| <= endpointResidual)
  (hfreeTrace : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity n c -> (Phi (embedding c)).im = 0) :
-- imply
  forall z, |faceDirichlet n hn z - faceSampledImaginaryTarget n embedding Phi z| <= faceBoundaryConsistencyError n hn (faceSampledImaginaryTarget n embedding Phi) + bulkResidual * faceExplicitPoissonBarrier n z + layerResidual * faceGhostLayerBarrier n z + endpointResidual * faceMarkedEndpointBarrier n radius z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSampled_target_error_le_endpointLocalized n hn radius embedding Phi bulkResidual layerResidual endpointResidual hbulkResidual hlayerResidual hendpointResidual hbulk hlayer hendpoint hfreeTrace

/--
[PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean)
-/
@[path]
private lemma primitive_convergence_away_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {bulkRate layerRate endpointRate : Nat -> Real}
  {H : PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius bulkRate layerRate endpointRate}
-- given
  (safe : forall k, FKIsingSquareInteriorRadialIncidence (N k) (hN k) -> Prop)
  (vertexEndpointWeight faceEndpointWeight mismatchRate : Nat -> Real)
  (hvertexWeight_nonneg : forall k, 0 <= vertexEndpointWeight k)
  (hfaceWeight_nonneg : forall k, 0 <= faceEndpointWeight k)
  (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
  (hvertexWeight : forall k e, safe k e -> vertexMarkedEndpointBarrier (N k) (radius k) (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) <= vertexEndpointWeight k)
  (hfaceWeight : forall k e, safe k e -> faceMarkedEndpointBarrier (N k) (radius k) (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) <= faceEndpointWeight k)
  (hmismatch : forall k e, safe k e -> |(Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| <= mismatchRate k)
  (hvertexEndpoint_tendsto : Tendsto (fun k => endpointRate k * vertexEndpointWeight k) atTop (nhds 0))
  (hfaceEndpoint_tendsto : Tendsto (fun k => endpointRate k * faceEndpointWeight k) atTop (nhds 0))
  (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
-- imply
  forall eta : Real, 0 < eta -> ∀ᶠ k in atTop, forall e : FKIsingSquareInteriorRadialIncidence (N k) (hN k), safe k e -> |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta /\ |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away H safe vertexEndpointWeight faceEndpointWeight mismatchRate hvertexWeight_nonneg hfaceWeight_nonneg hmismatch_nonneg hvertexWeight hfaceWeight hmismatch hvertexEndpoint_tendsto hfaceEndpoint_tendsto hmismatch_tendsto


-- created on 2026-10-23
