import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryClampedPrimitiveConvergence
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[PhysicalEndpointLocalizedClampedRobinInputs.vertex_error_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryClampedPrimitiveConvergence.lean)
-/
@[path]
private lemma vertex_error_le_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {bulkRate layerRate endpointRate : Nat -> Real}
  {H : PhysicalEndpointLocalizedClampedRobinInputs N hN Phi mesh radius bulkRate layerRate endpointRate}
  {k : Nat}
  {x : FKIsingSquareFullVertexNode (N k)}
-- given
  (hx : Not (fkIsingSquareFullVertexFixedBoundary (N k) x)) :
-- imply
  |vertexDirichlet (N k) (hN k) (some x) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <= bulkRate k * vertexExplicitPoissonBarrier (N k) (some x) + layerRate k * vertexGhostLayerBarrier (N k) (some x) + endpointRate k * vertexMarkedEndpointBarrier (N k) (radius k) (some x) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedClampedRobinInputs.vertex_error_le H k x hx

/--
[PhysicalEndpointLocalizedClampedRobinInputs.face_error_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryClampedPrimitiveConvergence.lean)
-/
@[path]
private lemma face_error_le_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {bulkRate layerRate endpointRate : Nat -> Real}
  {H : PhysicalEndpointLocalizedClampedRobinInputs N hN Phi mesh radius bulkRate layerRate endpointRate}
  {k : Nat}
  {c : FKIsingSquareFullFaceNode (N k)}
-- given
  (hc : Not (fkIsingSquareFullFaceFixedBoundary (N k) c)) :
-- imply
  |faceDirichlet (N k) (hN k) (some c) - (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| <= bulkRate k * faceExplicitPoissonBarrier (N k) (some c) + layerRate k * faceGhostLayerBarrier (N k) (some c) + endpointRate k * faceMarkedEndpointBarrier (N k) (radius k) (some c) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedClampedRobinInputs.face_error_le H k c hc

/--
[PhysicalEndpointLocalizedClampedRobinInputs.primitive_convergence_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryClampedPrimitiveConvergence.lean)
-/
@[path]
private lemma primitive_convergence_away_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {bulkRate layerRate endpointRate : Nat -> Real}
  {H : PhysicalEndpointLocalizedClampedRobinInputs N hN Phi mesh radius bulkRate layerRate endpointRate}
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
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedClampedRobinInputs.primitive_convergence_away H safe vertexEndpointWeight faceEndpointWeight mismatchRate hvertexWeight_nonneg hfaceWeight_nonneg hmismatch_nonneg hsafeVertex hsafeFace hvertexWeight hfaceWeight hmismatch hvertexEndpoint_tendsto hfaceEndpoint_tendsto hmismatch_tendsto

/--
[PhysicalEndpointLocalizedClampedRobinInputs.primitive_convergence_away_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryClampedPrimitiveConvergence.lean)
-/
@[path]
private lemma primitive_convergence_away_polynomial_eq
  {Phi : Complex -> Complex}
  {mesh bulkRate layerRate : Nat -> Real}
-- given
  (H : PhysicalEndpointLocalizedClampedRobinInputs isingFermionicPolynomialSide isingFermionicPolynomialSide_pos Phi mesh isingFermionicPolynomialRadius bulkRate layerRate (fun _ => 4))
  (mismatchRate : Nat -> Real)
  (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
  (hmismatch : forall k e, PhysicalPolynomialEndpointSafe k e -> |(Phi (fullSquareScaledFaceEmbedding (isingFermionicPolynomialSide k) (mesh k) (fkIsingSquareFullFaceOfRadialIncidence (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e))).im - (Phi (fullSquareScaledVertexEmbedding (isingFermionicPolynomialSide k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e))).im| <= mismatchRate k)
  (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
-- imply
  forall eta : Real, 0 < eta -> ∀ᶠ k in atTop, forall e : FKIsingSquareInteriorRadialIncidence (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k), PhysicalPolynomialEndpointSafe k e -> |(fkIsingSquareBoundaryLayerCoordinateOneForm (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e) - (Phi (fullSquareScaledVertexEmbedding (isingFermionicPolynomialSide k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e))).im| < eta /\ |(fkIsingSquareBoundaryLayerCoordinateOneForm (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e) - (Phi (fullSquareScaledVertexEmbedding (isingFermionicPolynomialSide k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e))).im| < eta := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedClampedRobinInputs.primitive_convergence_away_polynomial H mismatchRate hmismatch_nonneg hmismatch hmismatch_tendsto


-- created on 2026-10-23
