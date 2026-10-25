import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry.Part4
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[halfDiagonal_displacement_le_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean)
-/
@[path]
private lemma halfDiagonal_displacement_le_scale_eq
  {z direction : Complex}
  {scale : Real}
-- given
  (hdirection : ‖direction‖ <= 2)
  (hscale : 0 <= scale) :
-- imply
  dist z (z + ((scale / 2 : Real) : Complex) * direction) <= scale := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.halfDiagonal_displacement_le_scale z direction hdirection scale hscale

/--
[fullSquareVertexBoundaryProjection_mem_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean)
-/
@[path]
private lemma fullSquareVertexBoundaryProjection_mem_leftSide_eq
  {n : Nat}
  {scale : Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hx : fkIsingSquareFullVertexFixedBoundary n x) :
-- imply
  fullSquareVertexBoundaryProjection n scale x ∈ fullSquareScaledLeftSide n scale := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareVertexBoundaryProjection_mem_leftSide n scale x hx

/--
[fullSquareFaceFixedBoundaryProjection_mem_freeSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean)
-/
@[path]
private lemma fullSquareFaceFixedBoundaryProjection_mem_freeSides_eq
  {n : Nat}
  {scale : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hc : fkIsingSquareFullFaceFixedBoundary n c) :
-- imply
  fullSquareFaceFixedBoundaryProjection n scale c ∈ fullSquareScaledFreeSides n scale := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareFaceFixedBoundaryProjection_mem_freeSides n scale c hc

/--
[fullSquareVertexFreeBoundaryProjection_mem_freeSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean)
-/
@[path]
private lemma fullSquareVertexFreeBoundaryProjection_mem_freeSides_eq
  {n : Nat}
  {scale : Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hx : 0 < fkIsingSquareFullVertexGhostMultiplicity n x) :
-- imply
  fullSquareVertexFreeBoundaryProjection n scale x ∈ fullSquareScaledFreeSides n scale := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareVertexFreeBoundaryProjection_mem_freeSides n scale x hx

/--
[fullSquareFaceFreeBoundaryProjection_mem_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean)
-/
@[path]
private lemma fullSquareFaceFreeBoundaryProjection_mem_leftSide_eq
  {n : Nat}
  {scale : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hc : 0 < fkIsingSquareFullFaceGhostMultiplicity n c) :
-- imply
  fullSquareFaceFreeBoundaryProjection n scale c ∈ fullSquareScaledLeftSide n scale := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareFaceFreeBoundaryProjection_mem_leftSide n scale c hc

/--
[fullSquareVertexBoundaryProjection_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean)
-/
@[path]
private lemma fullSquareVertexBoundaryProjection_dist_eq
  {n : Nat}
  {scale : Real}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  dist (fullSquareScaledVertexEmbedding n scale x) (fullSquareVertexBoundaryProjection n scale x) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareVertexBoundaryProjection_dist n scale x

/--
[fullSquareFaceFixedBoundaryProjection_dist_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean)
-/
@[path]
private lemma fullSquareFaceFixedBoundaryProjection_dist_le_eq
  {n : Nat}
  {scale : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hscale : 0 <= scale) :
-- imply
  dist (fullSquareScaledFaceEmbedding n scale c) (fullSquareFaceFixedBoundaryProjection n scale c) <= scale := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareFaceFixedBoundaryProjection_dist_le n scale hscale c

/--
[fullSquareVertexFreeBoundaryProjection_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean)
-/
@[path]
private lemma fullSquareVertexFreeBoundaryProjection_dist_eq
  {n : Nat}
  {scale : Real}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  dist (fullSquareScaledVertexEmbedding n scale x) (fullSquareVertexFreeBoundaryProjection n scale x) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareVertexFreeBoundaryProjection_dist n scale x

/--
[fullSquareFaceFreeBoundaryProjection_dist_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean)
-/
@[path]
private lemma fullSquareFaceFreeBoundaryProjection_dist_le_eq
  {n : Nat}
  {scale : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hscale : 0 <= scale) :
-- imply
  dist (fullSquareScaledFaceEmbedding n scale c) (fullSquareFaceFreeBoundaryProjection n scale c) <= scale := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareFaceFreeBoundaryProjection_dist_le n scale hscale c

/--
[fullSquareOrdinaryBoundaryProjectionCarrier_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean)
-/
@[path]
private lemma fullSquareOrdinaryBoundaryProjectionCarrier_finite_eq
  {n : Nat}
  {mesh : Real}
  {radius : Nat} :
-- imply
  (fullSquareOrdinaryBoundaryProjectionCarrier n mesh radius).Finite := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareOrdinaryBoundaryProjectionCarrier_finite n mesh radius

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofCarrierTracesAndRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean)
-/
@[path]
private lemma ofCarrierTracesAndRange_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius}
  {Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius}
-- given
  (L : Nat -> NNReal)
  (hPhi : forall k, LipschitzOnWith (L k) (fun z => (Phi z).im) (fullSquareOrdinaryBoundaryProjectionCarrier (N k) (mesh k) (radius k)))
  (hvertexFixedTrace : forall k x, fkIsingSquareFullVertexFixedBoundary (N k) x -> Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) -> (Phi (fullSquareVertexBoundaryProjection (N k) (mesh k) x)).im = 0)
  (hfaceFixedTrace : forall k c, fkIsingSquareFullFaceFixedBoundary (N k) c -> Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) -> (Phi (fullSquareFaceFixedBoundaryProjection (N k) (mesh k) c)).im = 1)
  (hvertexFreeTrace : forall k x, Not (fkIsingSquareFullVertexFixedBoundary (N k) x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x -> Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) -> (Phi (fullSquareVertexFreeBoundaryProjection (N k) (mesh k) x)).im = 1)
  (hfaceFreeTrace : forall k c, Not (fkIsingSquareFullFaceFixedBoundary (N k) c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c -> Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) -> (Phi (fullSquareFaceFreeBoundaryProjection (N k) (mesh k) c)).im = 0)
  (hvertexRadius : forall k, 0 < radius k)
  (hfaceRadius : forall k, 2 <= radius k)
  (hmesh_nonneg : forall k, 0 <= mesh k)
  (hvertexRange : forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
  (hfaceRange : forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
  (hscaledFourth_tendsto : Tendsto (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
  (htrace_tendsto : Tendsto (fun k => (L k : Real) * mesh k) atTop (nhds 0))
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius (fun k => (L k : Real) * mesh k) (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * mesh k + (3 * isingFermionicGhostCoefficient) * ((L k : Real) * mesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofCarrierTracesAndRange Hfourth Hlayer L hPhi hvertexFixedTrace hfaceFixedTrace hvertexFreeTrace hfaceFreeTrace hvertexRadius hfaceRadius hmesh_nonneg hvertexRange hfaceRange hscaledFourth_tendsto htrace_tendsto hmesh_tendsto

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofCarrierSideTracesAndRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean)
-/
@[path]
private lemma ofCarrierSideTracesAndRange_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius}
  {Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius}
-- given
  (L : Nat -> NNReal)
  (hPhi : forall k, LipschitzOnWith (L k) (fun z => (Phi z).im) (fullSquareOrdinaryBoundaryProjectionCarrier (N k) (mesh k) (radius k)))
  (hleftTrace : forall k, Set.EqOn (fun z => (Phi z).im) (fun _ => 0) (fullSquareScaledLeftSide (N k) (mesh k)))
  (hfreeTrace : forall k, Set.EqOn (fun z => (Phi z).im) (fun _ => 1) (fullSquareScaledFreeSides (N k) (mesh k)))
  (hvertexRadius : forall k, 0 < radius k)
  (hfaceRadius : forall k, 2 <= radius k)
  (hmesh_nonneg : forall k, 0 <= mesh k)
  (hvertexRange : forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
  (hfaceRange : forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
  (hscaledFourth_tendsto : Tendsto (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
  (htrace_tendsto : Tendsto (fun k => (L k : Real) * mesh k) atTop (nhds 0))
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius (fun k => (L k : Real) * mesh k) (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * mesh k + (3 * isingFermionicGhostCoefficient) * ((L k : Real) * mesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofCarrierSideTracesAndRange Hfourth Hlayer L hPhi hleftTrace hfreeTrace hvertexRadius hfaceRadius hmesh_nonneg hvertexRange hfaceRange hscaledFourth_tendsto htrace_tendsto hmesh_tendsto


-- created on 2026-10-23
