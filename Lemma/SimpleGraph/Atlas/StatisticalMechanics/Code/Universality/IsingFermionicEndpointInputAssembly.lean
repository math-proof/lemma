import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointInputAssembly.Part2
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[PhysicalEndpointFourthOrderBulkData.vertexLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointInputAssembly.lean)
-/
@[path]
private lemma vertexLaplacian_eq
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {H : PhysicalEndpointFourthOrderBulkData N Phi mesh radius}
  {k : Nat}
  {x : FKIsingSquareFullVertexNode (N k)}
-- given
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
  (hghost : fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0)
  (hendpoint : Not (vertexMarkedEndpointLayer (N k) (radius k) (some x))) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y => (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im) x| <= (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointFourthOrderBulkData.vertexLaplacian H k x hfixed hghost hendpoint

/--
[PhysicalEndpointFourthOrderBulkData.faceLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointInputAssembly.lean)
-/
@[path]
private lemma faceLaplacian_eq
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {H : PhysicalEndpointFourthOrderBulkData N Phi mesh radius}
  {k : Nat}
  {c : FKIsingSquareFullFaceNode (N k)}
-- given
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
  (hghost : fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0)
  (hendpoint : Not (faceMarkedEndpointLayer (N k) (radius k) (some c))) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d => (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im) c| <= (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointFourthOrderBulkData.faceLaplacian H k c hfixed hghost hendpoint

/--
[PhysicalEndpointLocalizedRobinInputs.ofLocalizedFourthOrderAndRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointInputAssembly.lean)
-/
@[path]
private lemma ofLocalizedFourthOrderAndRange_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius}
-- given
  (layerRate : Nat -> Real)
  (hmesh_nonneg : forall k, 0 <= mesh k)
  (hlayer_nonneg : forall k, 0 <= layerRate k)
  (hvertexFixed : forall k x, fkIsingSquareFullVertexFixedBoundary (N k) x -> (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0)
  (hfaceFixed : forall k c, fkIsingSquareFullFaceFixedBoundary (N k) c -> (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1)
  (hvertexFree : forall k x, Not (fkIsingSquareFullVertexFixedBoundary (N k) x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x -> (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1)
  (hfaceFree : forall k c, Not (fkIsingSquareFullFaceFixedBoundary (N k) c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c -> (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0)
  (hvertexLayer : forall k x, Not (fkIsingSquareFullVertexFixedBoundary (N k) x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x -> Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) -> |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y => (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im) x| <= layerRate k)
  (hfaceLayer : forall k c, Not (fkIsingSquareFullFaceFixedBoundary (N k) c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c -> Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) -> |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d => (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im) c| <= layerRate k)
  (hvertexRange : forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
  (hfaceRange : forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
  (hscaledFourth_tendsto : Tendsto (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
  (hlayer_tendsto : Tendsto layerRate atTop (nhds 0))
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12) layerRate (fun _ => 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedRobinInputs.ofLocalizedFourthOrderAndRange layerRate Hfourth hmesh_nonneg hlayer_nonneg hvertexFixed hfaceFixed hvertexFree hfaceFree hvertexLayer hfaceLayer hvertexRange hfaceRange hscaledFourth_tendsto hlayer_tendsto hmesh_tendsto

/--
[PhysicalEndpointLayerIncrementData.vertexLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointInputAssembly.lean)
-/
@[path]
private lemma vertexLaplacian_eq_2
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {H : PhysicalEndpointLayerIncrementData N Phi mesh radius}
  {k : Nat}
  {x : FKIsingSquareFullVertexNode (N k)}
-- given
  (hmesh : forall k, 0 <= mesh k)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
  (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x)
  (hendpoint : Not (vertexMarkedEndpointLayer (N k) (radius k) (some x))) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y => (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im) x| <= 4 * H.constant * mesh k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLayerIncrementData.vertexLaplacian H hmesh k x hfixed hghost hendpoint

/--
[PhysicalEndpointLayerIncrementData.faceLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointInputAssembly.lean)
-/
@[path]
private lemma faceLaplacian_eq_2
  {N : Nat -> Nat}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {H : PhysicalEndpointLayerIncrementData N Phi mesh radius}
  {k : Nat}
  {c : FKIsingSquareFullFaceNode (N k)}
-- given
  (hmesh : forall k, 0 <= mesh k)
  (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
  (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c)
  (hendpoint : Not (faceMarkedEndpointLayer (N k) (radius k) (some c))) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d => (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im) c| <= 4 * H.constant * mesh k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLayerIncrementData.faceLaplacian H hmesh k c hfixed hghost hendpoint

/--
[PhysicalEndpointLocalizedRobinInputs.ofLocalizedFourthOrderLayerAndRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointInputAssembly.lean)
-/
@[path]
private lemma ofLocalizedFourthOrderLayerAndRange_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius}
  {Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius}
-- given
  (hmesh_nonneg : forall k, 0 <= mesh k)
  (hvertexFixed : forall k x, fkIsingSquareFullVertexFixedBoundary (N k) x -> (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0)
  (hfaceFixed : forall k c, fkIsingSquareFullFaceFixedBoundary (N k) c -> (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1)
  (hvertexFree : forall k x, Not (fkIsingSquareFullVertexFixedBoundary (N k) x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x -> (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1)
  (hfaceFree : forall k c, Not (fkIsingSquareFullFaceFixedBoundary (N k) c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c -> (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0)
  (hvertexRange : forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
  (hfaceRange : forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
  (hscaledFourth_tendsto : Tendsto (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12) (fun k => 4 * Hlayer.constant * mesh k) (fun _ => 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedRobinInputs.ofLocalizedFourthOrderLayerAndRange Hfourth Hlayer hmesh_nonneg hvertexFixed hfaceFixed hvertexFree hfaceFree hvertexRange hfaceRange hscaledFourth_tendsto hmesh_tendsto


-- created on 2026-10-23
