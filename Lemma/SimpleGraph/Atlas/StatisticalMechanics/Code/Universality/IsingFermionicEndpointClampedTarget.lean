import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointClampedTarget.Part3
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[boundaryTrace_abs_sub_le_of_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma boundaryTrace_abs_sub_le_of_lipschitz_eq
  {L : NNReal}
  {sample boundaryPoint : Complex}
  {value mesh : Real}
-- given
  (Phi : Complex -> Complex)
  (hPhi : LipschitzWith L (fun z => (Phi z).im))
  (htrace : (Phi boundaryPoint).im = value)
  (hdist : dist sample boundaryPoint <= mesh) :
-- imply
  |value - (Phi sample).im| <= L * mesh := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.boundaryTrace_abs_sub_le_of_lipschitz Phi L hPhi sample boundaryPoint value mesh htrace hdist

/--
[isingFiniteGraphLaplacian_boundaryClamp_sub_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma isingFiniteGraphLaplacian_boundaryClamp_sub_le_four_eq
  [Fintype V]
  {G : SimpleGraph V}
  {value : Real}
  {x : V}
  {traceBound : Real}
-- given
  (boundary : V -> Prop)
  (f : V -> Real)
  (hx : Not (boundary x))
  (htrace_nonneg : 0 <= traceBound)
  (hcard : Nat.card (G.neighborSet x) <= 4)
  (htrace : forall y, boundary y -> |value - f y| <= traceBound) :
-- imply
  |isingFiniteGraphLaplacian G (isingBoundaryClamp boundary value f) x - isingFiniteGraphLaplacian G f x| <= 4 * traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFiniteGraphLaplacian_boundaryClamp_sub_le_four G boundary value f x hx traceBound htrace_nonneg hcard htrace

/--
[isingFiniteGhostLaplacian_boundaryClamp_sub_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma isingFiniteGhostLaplacian_boundaryClamp_sub_le_four_eq
  [Fintype V]
  {G : SimpleGraph V}
  {value ghostValue : Real}
  {x : V}
  {traceBound : Real}
-- given
  (ghostRate : V -> Real)
  (boundary : V -> Prop)
  (f : V -> Real)
  (hx : Not (boundary x))
  (htrace_nonneg : 0 <= traceBound)
  (hcard : Nat.card (G.neighborSet x) <= 4)
  (htrace : forall y, boundary y -> |value - f y| <= traceBound) :
-- imply
  |isingFiniteWeightedLaplacian (isingFiniteGhostConductance G ghostRate) (isingFiniteGhostExtension ghostValue (isingBoundaryClamp boundary value f)) (some x) - isingFiniteWeightedLaplacian (isingFiniteGhostConductance G ghostRate) (isingFiniteGhostExtension ghostValue f) (some x)| <= 4 * traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFiniteGhostLaplacian_boundaryClamp_sub_le_four G ghostRate boundary value ghostValue f x hx traceBound htrace_nonneg hcard htrace

/--
[vertexBoundaryClampedSampledTarget_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma vertexBoundaryClampedSampledTarget_none_eq
  {n : Nat}
-- given
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex) :
-- imply
  vertexBoundaryClampedSampledTarget n embedding Phi none = 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBoundaryClampedSampledTarget_none n embedding Phi

/--
[faceBoundaryClampedSampledTarget_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma faceBoundaryClampedSampledTarget_none_eq
  {n : Nat}
-- given
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex) :
-- imply
  faceBoundaryClampedSampledTarget n embedding Phi none = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceBoundaryClampedSampledTarget_none n embedding Phi

/--
[vertexBoundaryClampedSampledTarget_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma vertexBoundaryClampedSampledTarget_of_fixed_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex)
  (hx : fkIsingSquareFullVertexFixedBoundary n x) :
-- imply
  vertexBoundaryClampedSampledTarget n embedding Phi (some x) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBoundaryClampedSampledTarget_of_fixed n embedding Phi x hx

/--
[faceBoundaryClampedSampledTarget_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma faceBoundaryClampedSampledTarget_of_fixed_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex)
  (hc : fkIsingSquareFullFaceFixedBoundary n c) :
-- imply
  faceBoundaryClampedSampledTarget n embedding Phi (some c) = 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceBoundaryClampedSampledTarget_of_fixed n embedding Phi c hc

/--
[vertexBoundaryClampedSampledTarget_of_not_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma vertexBoundaryClampedSampledTarget_of_not_fixed_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex)
  (hx : Not (fkIsingSquareFullVertexFixedBoundary n x)) :
-- imply
  vertexBoundaryClampedSampledTarget n embedding Phi (some x) = (Phi (embedding x)).im := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBoundaryClampedSampledTarget_of_not_fixed n embedding Phi x hx

/--
[faceBoundaryClampedSampledTarget_of_not_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma faceBoundaryClampedSampledTarget_of_not_fixed_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex)
  (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
-- imply
  faceBoundaryClampedSampledTarget n embedding Phi (some c) = (Phi (embedding c)).im := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceBoundaryClampedSampledTarget_of_not_fixed n embedding Phi c hc

/--
[vertexBoundaryClampedSampledTarget_boundaryConsistencyError_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma vertexBoundaryClampedSampledTarget_boundaryConsistencyError_eq_zero_eq
  {n : Nat}
-- given
  (hn : 0 < n)
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex) :
-- imply
  vertexBoundaryConsistencyError n hn (vertexBoundaryClampedSampledTarget n embedding Phi) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBoundaryClampedSampledTarget_boundaryConsistencyError_eq_zero n hn embedding Phi

/--
[faceBoundaryClampedSampledTarget_boundaryConsistencyError_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma faceBoundaryClampedSampledTarget_boundaryConsistencyError_eq_zero_eq
  {n : Nat}
-- given
  (hn : 0 < n)
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex) :
-- imply
  faceBoundaryConsistencyError n hn (faceBoundaryClampedSampledTarget n embedding Phi) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceBoundaryClampedSampledTarget_boundaryConsistencyError_eq_zero n hn embedding Phi

/--
[vertexBoundaryClampedSampledTarget_laplacian_sub_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma vertexBoundaryClampedSampledTarget_laplacian_sub_le_four_eq
  {n : Nat}
  {traceBound : Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex)
  (htrace_nonneg : 0 <= traceBound)
  (htrace : forall y, fkIsingSquareFullVertexFixedBoundary n y -> |0 - (Phi (embedding y)).im| <= traceBound)
  (hx : Not (fkIsingSquareFullVertexFixedBoundary n x)) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => vertexBoundaryClampedSampledTarget n embedding Phi (some y)) x - isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => (Phi (embedding y)).im) x| <= 4 * traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBoundaryClampedSampledTarget_laplacian_sub_le_four n embedding Phi traceBound htrace_nonneg htrace x hx

/--
[faceBoundaryClampedSampledTarget_laplacian_sub_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma faceBoundaryClampedSampledTarget_laplacian_sub_le_four_eq
  {n : Nat}
  {traceBound : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex)
  (htrace_nonneg : 0 <= traceBound)
  (htrace : forall d, fkIsingSquareFullFaceFixedBoundary n d -> |1 - (Phi (embedding d)).im| <= traceBound)
  (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d => faceBoundaryClampedSampledTarget n embedding Phi (some d)) c - isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d => (Phi (embedding d)).im) c| <= 4 * traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceBoundaryClampedSampledTarget_laplacian_sub_le_four n embedding Phi traceBound htrace_nonneg htrace c hc

/--
[vertexBoundaryClampedSampledTarget_weightedLaplacian_sub_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma vertexBoundaryClampedSampledTarget_weightedLaplacian_sub_le_four_eq
  {n : Nat}
  {traceBound : Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex)
  (htrace_nonneg : 0 <= traceBound)
  (htrace : forall y, fkIsingSquareFullVertexFixedBoundary n y -> |0 - (Phi (embedding y)).im| <= traceBound)
  (hx : Not (fkIsingSquareFullVertexFixedBoundary n x)) :
-- imply
  |isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexBoundaryClampedSampledTarget n embedding Phi) (some x) - isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexSampledImaginaryTarget n embedding Phi) (some x)| <= 4 * traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBoundaryClampedSampledTarget_weightedLaplacian_sub_le_four n embedding Phi traceBound htrace_nonneg htrace x hx

/--
[faceBoundaryClampedSampledTarget_weightedLaplacian_sub_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma faceBoundaryClampedSampledTarget_weightedLaplacian_sub_le_four_eq
  {n : Nat}
  {traceBound : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex)
  (htrace_nonneg : 0 <= traceBound)
  (htrace : forall d, fkIsingSquareFullFaceFixedBoundary n d -> |1 - (Phi (embedding d)).im| <= traceBound)
  (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
-- imply
  |isingFiniteWeightedLaplacian (faceGhostConductance n) (faceBoundaryClampedSampledTarget n embedding Phi) (some c) - isingFiniteWeightedLaplacian (faceGhostConductance n) (faceSampledImaginaryTarget n embedding Phi) (some c)| <= 4 * traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceBoundaryClampedSampledTarget_weightedLaplacian_sub_le_four n embedding Phi traceBound htrace_nonneg htrace c hc

/--
[vertexBoundaryClampedSampledTarget_laplacian_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma vertexBoundaryClampedSampledTarget_laplacian_le_eq
  {n : Nat}
  {sampleBound traceBound : Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex)
  (htrace_nonneg : 0 <= traceBound)
  (htrace : forall y, fkIsingSquareFullVertexFixedBoundary n y -> |0 - (Phi (embedding y)).im| <= traceBound)
  (hx : Not (fkIsingSquareFullVertexFixedBoundary n x))
  (hsample : |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => (Phi (embedding y)).im) x| <= sampleBound) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => vertexBoundaryClampedSampledTarget n embedding Phi (some y)) x| <= sampleBound + 4 * traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBoundaryClampedSampledTarget_laplacian_le n embedding Phi sampleBound traceBound htrace_nonneg htrace x hx hsample

/--
[faceBoundaryClampedSampledTarget_laplacian_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma faceBoundaryClampedSampledTarget_laplacian_le_eq
  {n : Nat}
  {sampleBound traceBound : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex)
  (htrace_nonneg : 0 <= traceBound)
  (htrace : forall d, fkIsingSquareFullFaceFixedBoundary n d -> |1 - (Phi (embedding d)).im| <= traceBound)
  (hc : Not (fkIsingSquareFullFaceFixedBoundary n c))
  (hsample : |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d => (Phi (embedding d)).im) c| <= sampleBound) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d => faceBoundaryClampedSampledTarget n embedding Phi (some d)) c| <= sampleBound + 4 * traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceBoundaryClampedSampledTarget_laplacian_le n embedding Phi sampleBound traceBound htrace_nonneg htrace c hc hsample

/--
[vertexBoundaryClampedSampledTarget_error_le_endpointLocalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma vertexBoundaryClampedSampledTarget_error_le_endpointLocalized_eq
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
  (hbulk : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> fkIsingSquareFullVertexGhostMultiplicity n x = 0 -> Not (vertexMarkedEndpointLayer n radius (some x)) -> |isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexBoundaryClampedSampledTarget n embedding Phi) (some x)| <= bulkResidual)
  (hlayer : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity n x -> Not (vertexMarkedEndpointLayer n radius (some x)) -> |isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexBoundaryClampedSampledTarget n embedding Phi) (some x)| <= layerResidual)
  (hendpoint : forall x, Not (fkIsingSquareFullVertexFixedBoundary n x) -> vertexMarkedEndpointLayer n radius (some x) -> |isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexBoundaryClampedSampledTarget n embedding Phi) (some x)| <= endpointResidual) :
-- imply
  forall z, |vertexDirichlet n hn z - vertexBoundaryClampedSampledTarget n embedding Phi z| <= bulkResidual * vertexExplicitPoissonBarrier n z + layerResidual * vertexGhostLayerBarrier n z + endpointResidual * vertexMarkedEndpointBarrier n radius z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBoundaryClampedSampledTarget_error_le_endpointLocalized n hn radius embedding Phi bulkResidual layerResidual endpointResidual hbulkResidual hlayerResidual hendpointResidual hbulk hlayer hendpoint

/--
[faceBoundaryClampedSampledTarget_error_le_endpointLocalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean)
-/
@[path]
private lemma faceBoundaryClampedSampledTarget_error_le_endpointLocalized_eq
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
  (hbulk : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> fkIsingSquareFullFaceGhostMultiplicity n c = 0 -> Not (faceMarkedEndpointLayer n radius (some c)) -> |isingFiniteWeightedLaplacian (faceGhostConductance n) (faceBoundaryClampedSampledTarget n embedding Phi) (some c)| <= bulkResidual)
  (hlayer : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity n c -> Not (faceMarkedEndpointLayer n radius (some c)) -> |isingFiniteWeightedLaplacian (faceGhostConductance n) (faceBoundaryClampedSampledTarget n embedding Phi) (some c)| <= layerResidual)
  (hendpoint : forall c, Not (fkIsingSquareFullFaceFixedBoundary n c) -> faceMarkedEndpointLayer n radius (some c) -> |isingFiniteWeightedLaplacian (faceGhostConductance n) (faceBoundaryClampedSampledTarget n embedding Phi) (some c)| <= endpointResidual) :
-- imply
  forall z, |faceDirichlet n hn z - faceBoundaryClampedSampledTarget n embedding Phi z| <= bulkResidual * faceExplicitPoissonBarrier n z + layerResidual * faceGhostLayerBarrier n z + endpointResidual * faceMarkedEndpointBarrier n radius z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceBoundaryClampedSampledTarget_error_le_endpointLocalized n hn radius embedding Phi bulkResidual layerResidual endpointResidual hbulkResidual hlayerResidual hendpointResidual hbulk hlayer hendpoint


-- created on 2026-10-23
