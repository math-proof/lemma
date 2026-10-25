import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk.Part2
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[PhysicalEndpointVariableFourthOrderBulkData.vertexLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVariableFourthOrderBulk.lean)
-/
@[path]
private lemma vertexLaplacian_eq
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {H : PhysicalEndpointVariableFourthOrderBulkData N Phi mesh radius}
  {k : Nat}
  {x : FKIsingSquareFullVertexNode (N k)}
-- given
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
  (hghost : fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0)
  (hendpoint : Not (vertexMarkedEndpointLayer (N k) (radius k) (some x))) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y => (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im) x| <= (H.boundOne k + H.boundTwo k) * |mesh k| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointVariableFourthOrderBulkData.vertexLaplacian H k x hfixed hghost hendpoint

/--
[PhysicalEndpointVariableFourthOrderBulkData.faceLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVariableFourthOrderBulk.lean)
-/
@[path]
private lemma faceLaplacian_eq
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {H : PhysicalEndpointVariableFourthOrderBulkData N Phi mesh radius}
  {k : Nat}
  {c : FKIsingSquareFullFaceNode (N k)}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
  (hghost : fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0)
  (hendpoint : Not (faceMarkedEndpointLayer (N k) (radius k) (some c))) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d => (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im) c| <= (H.boundOne k + H.boundTwo k) * |mesh k| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointVariableFourthOrderBulkData.faceLaplacian H k c hfixed hghost hendpoint

/--
[PhysicalEndpointVariableLayerIncrementData.vertexLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVariableFourthOrderBulk.lean)
-/
@[path]
private lemma vertexLaplacian_eq_2
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {H : PhysicalEndpointVariableLayerIncrementData N Phi mesh radius}
  {k : Nat}
  {x : FKIsingSquareFullVertexNode (N k)}
-- given
  (hmesh : forall k, 0 <= mesh k)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
  (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x)
  (hendpoint : Not (vertexMarkedEndpointLayer (N k) (radius k) (some x))) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y => (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im) x| <= 4 * H.constant k * mesh k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointVariableLayerIncrementData.vertexLaplacian H hmesh k x hfixed hghost hendpoint

/--
[PhysicalEndpointVariableLayerIncrementData.faceLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVariableFourthOrderBulk.lean)
-/
@[path]
private lemma faceLaplacian_eq_2
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {H : PhysicalEndpointVariableLayerIncrementData N Phi mesh radius}
  {k : Nat}
  {c : FKIsingSquareFullFaceNode (N k)}
-- given
  (hmesh : forall k, 0 <= mesh k)
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
  (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c)
  (hendpoint : Not (faceMarkedEndpointLayer (N k) (radius k) (some c))) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d => (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im) c| <= 4 * H.constant k * mesh k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointVariableLayerIncrementData.faceLaplacian H hmesh k c hfixed hghost hendpoint

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofVariableFourthOrderLayerTraceAndRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVariableFourthOrderBulk.lean)
-/
@[path]
private lemma ofVariableFourthOrderLayerTraceAndRange_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {traceRate : Nat -> Real}
  {Hfourth : PhysicalEndpointVariableFourthOrderBulkData N Phi mesh radius}
  {Hlayer : PhysicalEndpointVariableLayerIncrementData N Phi mesh radius}
  {Htrace : PhysicalEndpointOrdinaryTraceData N Phi mesh radius traceRate}
-- given
  (hvertexRadius : forall k, 0 < radius k)
  (hfaceRadius : forall k, 2 <= radius k)
  (hmesh_nonneg : forall k, 0 <= mesh k)
  (hvertexRange : forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
  (hfaceRange : forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
  (hscaledFourth_tendsto : Tendsto (fun k => ((Hfourth.boundOne k + Hfourth.boundTwo k) * |mesh k| ^ 4 / 12) * (N k : Real) ^ 2) atTop (nhds 0))
  (hlayer_tendsto : Tendsto (fun k => (Hlayer.constant k : Real) * mesh k) atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius traceRate (fun k => (Hfourth.boundOne k + Hfourth.boundTwo k) * |mesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant k) * mesh k + (3 * isingFermionicGhostCoefficient) * traceRate k) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofVariableFourthOrderLayerTraceAndRange Hfourth Hlayer Htrace hvertexRadius hfaceRadius hmesh_nonneg hvertexRange hfaceRange hscaledFourth_tendsto hlayer_tendsto


-- created on 2026-10-23
