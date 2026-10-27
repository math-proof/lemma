import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionFixedDomain.Part3
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[isingFermionicFixedDiamondMesh_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma isingFermionicFixedDiamondMesh_nonneg_eq
  {k : Nat} :
-- imply
  0 <= isingFermionicFixedDiamondMesh k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFermionicFixedDiamondMesh_nonneg k

/--
[isingFermionicProjectionPolynomialSide_mul_fixedDiamondMesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma isingFermionicProjectionPolynomialSide_mul_fixedDiamondMesh_eq
  {k : Nat} :
-- imply
  (isingFermionicProjectionPolynomialSide k : Real) * isingFermionicFixedDiamondMesh k = 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFermionicProjectionPolynomialSide_mul_fixedDiamondMesh k

/--
[isingFermionicFixedDiamondMesh_eq_inv_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma isingFermionicFixedDiamondMesh_eq_inv_pow_eq
  {k : Nat} :
-- imply
  isingFermionicFixedDiamondMesh k = (1 / ((k : Real) + 2)) ^ 5 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFermionicFixedDiamondMesh_eq_inv_pow k

/--
[tendsto_isingFermionicFixedDiamondMesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma tendsto_isingFermionicFixedDiamondMesh_eq :
-- imply
  Tendsto isingFermionicFixedDiamondMesh atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_isingFermionicFixedDiamondMesh

/--
[tendsto_isingFermionicFixedDiamondMesh_fourthOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma tendsto_isingFermionicFixedDiamondMesh_fourthOrder_eq :
-- imply
  Tendsto (fun k => |isingFermionicFixedDiamondMesh k| ^ 4 * (isingFermionicProjectionPolynomialSide k : Real) ^ 2) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_isingFermionicFixedDiamondMesh_fourthOrder

/--
[tendsto_isingFermionicProjectionQuadraticLipschitz_mul_fixedDiamondMesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma tendsto_isingFermionicProjectionQuadraticLipschitz_mul_fixedDiamondMesh_eq
  {C : NNReal} :
-- imply
  Tendsto (fun k => (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) * isingFermionicFixedDiamondMesh k) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_isingFermionicProjectionQuadraticLipschitz_mul_fixedDiamondMesh C

/--
[tendsto_isingFermionicFixedDiamondEndpointLipschitz_mul_mesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma tendsto_isingFermionicFixedDiamondEndpointLipschitz_mul_mesh_eq
  {C : NNReal} :
-- imply
  Tendsto (fun k => (isingFermionicFixedDiamondEndpointLipschitzConstant C k : Real) * isingFermionicFixedDiamondMesh k) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_isingFermionicFixedDiamondEndpointLipschitz_mul_mesh C

/--
[fullSquareScaledVertexEmbedding_mem_fixedClosedDiamond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma fullSquareScaledVertexEmbedding_mem_fixedClosedDiamond_eq
  {k : Nat}
  {x : FKIsingSquareFullVertexNode (isingFermionicProjectionPolynomialSide k)} :
-- imply
  fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) x ∈ isingFermionicFixedClosedDiamond := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding_mem_fixedClosedDiamond k x

/--
[fullSquareScaledFaceEmbedding_mem_fixedClosedDiamond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma fullSquareScaledFaceEmbedding_mem_fixedClosedDiamond_eq
  {k : Nat}
  {c : FKIsingSquareFullFaceNode (isingFermionicProjectionPolynomialSide k)} :
-- imply
  fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) c ∈ isingFermionicFixedClosedDiamond := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFaceEmbedding_mem_fixedClosedDiamond k c

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.fixedDiamondRanges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma fixedDiamondRanges_eq
  {Phi : Complex -> Complex}
-- given
  (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond isingFermionicClosedUnitStrip) :
-- imply
  (forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) x)).im <= 1) /\ (forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) c)).im <= 1) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.fixedDiamondRanges hrange

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondVariableFourthOrderTraceDataAndMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma ofFixedDiamondVariableFourthOrderTraceDataAndMap_eq
  {Phi : Complex -> Complex}
  {Hfourth : PhysicalEndpointVariableFourthOrderBulkData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {Hlayer : PhysicalEndpointVariableLayerIncrementData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {Htrace : FullSquareOrdinaryBoundaryProjectionTraceData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
-- given
  (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond isingFermionicClosedUnitStrip)
  (hscaledFourth_tendsto : Tendsto (fun k => ((Hfourth.boundOne k + Hfourth.boundTwo k) * |isingFermionicFixedDiamondMesh k| ^ 4 / 12) * (isingFermionicProjectionPolynomialSide k : Real) ^ 2) atTop (nhds 0))
  (htrace_tendsto : Tendsto (fun k => (Htrace.lipschitzConstant k : Real) * isingFermionicFixedDiamondMesh k) atTop (nhds 0))
  (hlayer_tendsto : Tendsto (fun k => (Hlayer.constant k : Real) * isingFermionicFixedDiamondMesh k) atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicProjectionPolynomialSide isingFermionicProjectionPolynomialSide_pos Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius (fun k => (Htrace.lipschitzConstant k : Real) * isingFermionicFixedDiamondMesh k) (fun k => (Hfourth.boundOne k + Hfourth.boundTwo k) * |isingFermionicFixedDiamondMesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant k) * isingFermionicFixedDiamondMesh k + (3 * isingFermionicGhostCoefficient) * ((Htrace.lipschitzConstant k : Real) * isingFermionicFixedDiamondMesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondVariableFourthOrderTraceDataAndMap Hfourth Hlayer Htrace hrange hscaledFourth_tendsto htrace_tendsto hlayer_tendsto

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondOrdinaryTracesAndRangeWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma ofFixedDiamondOrdinaryTracesAndRangeWith_eq
  {Phi : Complex -> Complex}
  {Hfourth : PhysicalEndpointFourthOrderBulkData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {Hlayer : PhysicalEndpointLayerIncrementData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
-- given
  (L : Nat -> NNReal)
  (hPhi : forall k, LipschitzOnWith (L k) (fun z => (Phi z).im) (fullSquareOrdinaryBoundaryProjectionCarrier (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (isingFermionicProjectionPolynomialRadius k)))
  (hvertexFixedTrace : forall k x, fkIsingSquareFullVertexFixedBoundary (isingFermionicProjectionPolynomialSide k) x -> Not (0 < fkIsingSquareFullVertexGhostMultiplicity (isingFermionicProjectionPolynomialSide k) x) -> (Phi (fullSquareVertexBoundaryProjection (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) x)).im = 0)
  (hfaceFixedTrace : forall k c, fkIsingSquareFullFaceFixedBoundary (isingFermionicProjectionPolynomialSide k) c -> Not (0 < fkIsingSquareFullFaceGhostMultiplicity (isingFermionicProjectionPolynomialSide k) c) -> (Phi (fullSquareFaceFixedBoundaryProjection (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) c)).im = 1)
  (hvertexFreeTrace : forall k x, Not (fkIsingSquareFullVertexFixedBoundary (isingFermionicProjectionPolynomialSide k) x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity (isingFermionicProjectionPolynomialSide k) x -> Not (vertexMarkedEndpointLayer (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialRadius k) (some x)) -> (Phi (fullSquareVertexFreeBoundaryProjection (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) x)).im = 1)
  (hfaceFreeTrace : forall k c, Not (fkIsingSquareFullFaceFixedBoundary (isingFermionicProjectionPolynomialSide k) c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity (isingFermionicProjectionPolynomialSide k) c -> Not (faceMarkedEndpointLayer (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialRadius k) (some c)) -> (Phi (fullSquareFaceFreeBoundaryProjection (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) c)).im = 0)
  (hvertexRange : forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) x)).im <= 1)
  (hfaceRange : forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) c)).im <= 1)
  (htrace_tendsto : Tendsto (fun k => (L k : Real) * isingFermionicFixedDiamondMesh k) atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicProjectionPolynomialSide isingFermionicProjectionPolynomialSide_pos Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius (fun k => (L k : Real) * isingFermionicFixedDiamondMesh k) (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |isingFermionicFixedDiamondMesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k + (3 * isingFermionicGhostCoefficient) * ((L k : Real) * isingFermionicFixedDiamondMesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondOrdinaryTracesAndRangeWith Hfourth Hlayer L hPhi hvertexFixedTrace hfaceFixedTrace hvertexFreeTrace hfaceFreeTrace hvertexRange hfaceRange htrace_tendsto

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondOrdinaryTracesAndMapWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma ofFixedDiamondOrdinaryTracesAndMapWith_eq
  {Phi : Complex -> Complex}
  {Hfourth : PhysicalEndpointFourthOrderBulkData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {Hlayer : PhysicalEndpointLayerIncrementData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
-- given
  (L : Nat -> NNReal)
  (hPhi : forall k, LipschitzOnWith (L k) (fun z => (Phi z).im) (fullSquareOrdinaryBoundaryProjectionCarrier (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (isingFermionicProjectionPolynomialRadius k)))
  (hvertexFixedTrace : forall k x, fkIsingSquareFullVertexFixedBoundary (isingFermionicProjectionPolynomialSide k) x -> Not (0 < fkIsingSquareFullVertexGhostMultiplicity (isingFermionicProjectionPolynomialSide k) x) -> (Phi (fullSquareVertexBoundaryProjection (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) x)).im = 0)
  (hfaceFixedTrace : forall k c, fkIsingSquareFullFaceFixedBoundary (isingFermionicProjectionPolynomialSide k) c -> Not (0 < fkIsingSquareFullFaceGhostMultiplicity (isingFermionicProjectionPolynomialSide k) c) -> (Phi (fullSquareFaceFixedBoundaryProjection (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) c)).im = 1)
  (hvertexFreeTrace : forall k x, Not (fkIsingSquareFullVertexFixedBoundary (isingFermionicProjectionPolynomialSide k) x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity (isingFermionicProjectionPolynomialSide k) x -> Not (vertexMarkedEndpointLayer (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialRadius k) (some x)) -> (Phi (fullSquareVertexFreeBoundaryProjection (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) x)).im = 1)
  (hfaceFreeTrace : forall k c, Not (fkIsingSquareFullFaceFixedBoundary (isingFermionicProjectionPolynomialSide k) c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity (isingFermionicProjectionPolynomialSide k) c -> Not (faceMarkedEndpointLayer (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialRadius k) (some c)) -> (Phi (fullSquareFaceFreeBoundaryProjection (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) c)).im = 0)
  (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond isingFermionicClosedUnitStrip)
  (htrace_tendsto : Tendsto (fun k => (L k : Real) * isingFermionicFixedDiamondMesh k) atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicProjectionPolynomialSide isingFermionicProjectionPolynomialSide_pos Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius (fun k => (L k : Real) * isingFermionicFixedDiamondMesh k) (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |isingFermionicFixedDiamondMesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k + (3 * isingFermionicGhostCoefficient) * ((L k : Real) * isingFermionicFixedDiamondMesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondOrdinaryTracesAndMapWith Hfourth Hlayer L hPhi hvertexFixedTrace hfaceFixedTrace hvertexFreeTrace hfaceFreeTrace hrange htrace_tendsto

/--
[fullSquareScaledLeftSide_fixedDiamond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma fullSquareScaledLeftSide_fixedDiamond_eq
  {k : Nat} :
-- imply
  fullSquareScaledLeftSide (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) = isingFermionicFixedDiamondLeftSide := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledLeftSide_fixedDiamond k

/--
[fullSquareScaledFreeSides_fixedDiamond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma fullSquareScaledFreeSides_fixedDiamond_eq
  {k : Nat} :
-- imply
  fullSquareScaledFreeSides (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) = isingFermionicFixedDiamondFreeSides := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFreeSides_fixedDiamond k

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondCarrierTracesAndRangeWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma ofFixedDiamondCarrierTracesAndRangeWith_eq
  {Phi : Complex -> Complex}
  {Hfourth : PhysicalEndpointFourthOrderBulkData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {Hlayer : PhysicalEndpointLayerIncrementData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
-- given
  (L : Nat -> NNReal)
  (hPhi : forall k, LipschitzOnWith (L k) (fun z => (Phi z).im) (fullSquareOrdinaryBoundaryProjectionCarrier (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (isingFermionicProjectionPolynomialRadius k)))
  (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0) isingFermionicFixedDiamondLeftSide)
  (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1) isingFermionicFixedDiamondFreeSides)
  (hvertexRange : forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) x)).im <= 1)
  (hfaceRange : forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) c)).im <= 1)
  (htrace_tendsto : Tendsto (fun k => (L k : Real) * isingFermionicFixedDiamondMesh k) atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicProjectionPolynomialSide isingFermionicProjectionPolynomialSide_pos Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius (fun k => (L k : Real) * isingFermionicFixedDiamondMesh k) (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |isingFermionicFixedDiamondMesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k + (3 * isingFermionicGhostCoefficient) * ((L k : Real) * isingFermionicFixedDiamondMesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondCarrierTracesAndRangeWith Hfourth Hlayer L hPhi hleftTrace hfreeTrace hvertexRange hfaceRange htrace_tendsto

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondCarrierTracesAndRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma ofFixedDiamondCarrierTracesAndRange_eq
  {Phi : Complex -> Complex}
  {Hfourth : PhysicalEndpointFourthOrderBulkData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {Hlayer : PhysicalEndpointLayerIncrementData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {C : NNReal}
-- given
  (hPhi : forall k, LipschitzOnWith (isingFermionicQuadraticLipschitzConstant C (k + 1)) (fun z => (Phi z).im) (fullSquareOrdinaryBoundaryProjectionCarrier (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (isingFermionicProjectionPolynomialRadius k)))
  (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0) isingFermionicFixedDiamondLeftSide)
  (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1) isingFermionicFixedDiamondFreeSides)
  (hvertexRange : forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) x)).im <= 1)
  (hfaceRange : forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) c)).im <= 1) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicProjectionPolynomialSide isingFermionicProjectionPolynomialSide_pos Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius (fun k => (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) * isingFermionicFixedDiamondMesh k) (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |isingFermionicFixedDiamondMesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k + (3 * isingFermionicGhostCoefficient) * ((isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) * isingFermionicFixedDiamondMesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondCarrierTracesAndRange Hfourth Hlayer C hPhi hleftTrace hfreeTrace hvertexRange hfaceRange

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondMapWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma ofFixedDiamondMapWith_eq
  {Phi : Complex -> Complex}
  {Hfourth : PhysicalEndpointFourthOrderBulkData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {Hlayer : PhysicalEndpointLayerIncrementData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
-- given
  (L : Nat -> NNReal)
  (hPhi : forall k, LipschitzOnWith (L k) (fun z => (Phi z).im) (fullSquareOrdinaryBoundaryProjectionCarrier (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (isingFermionicProjectionPolynomialRadius k)))
  (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0) isingFermionicFixedDiamondLeftSide)
  (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1) isingFermionicFixedDiamondFreeSides)
  (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond isingFermionicClosedUnitStrip)
  (htrace_tendsto : Tendsto (fun k => (L k : Real) * isingFermionicFixedDiamondMesh k) atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicProjectionPolynomialSide isingFermionicProjectionPolynomialSide_pos Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius (fun k => (L k : Real) * isingFermionicFixedDiamondMesh k) (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |isingFermionicFixedDiamondMesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k + (3 * isingFermionicGhostCoefficient) * ((L k : Real) * isingFermionicFixedDiamondMesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondMapWith Hfourth Hlayer L hPhi hleftTrace hfreeTrace hrange htrace_tendsto

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma ofFixedDiamondMap_eq
  {Phi : Complex -> Complex}
  {Hfourth : PhysicalEndpointFourthOrderBulkData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {Hlayer : PhysicalEndpointLayerIncrementData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {C : NNReal}
-- given
  (hPhi : forall k, LipschitzOnWith (isingFermionicQuadraticLipschitzConstant C (k + 1)) (fun z => (Phi z).im) (fullSquareOrdinaryBoundaryProjectionCarrier (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (isingFermionicProjectionPolynomialRadius k)))
  (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0) isingFermionicFixedDiamondLeftSide)
  (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1) isingFermionicFixedDiamondFreeSides)
  (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond isingFermionicClosedUnitStrip) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicProjectionPolynomialSide isingFermionicProjectionPolynomialSide_pos Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius (fun k => (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) * isingFermionicFixedDiamondMesh k) (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |isingFermionicFixedDiamondMesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k + (3 * isingFermionicGhostCoefficient) * ((isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) * isingFermionicFixedDiamondMesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondMap Hfourth Hlayer C hPhi hleftTrace hfreeTrace hrange

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondEndpointLipschitzMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma ofFixedDiamondEndpointLipschitzMap_eq
  {Phi : Complex -> Complex}
  {Hfourth : PhysicalEndpointFourthOrderBulkData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {Hlayer : PhysicalEndpointLayerIncrementData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {C : NNReal}
-- given
  (hPhi : forall k, LipschitzOnWith (isingFermionicFixedDiamondEndpointLipschitzConstant C k) (fun z => (Phi z).im) (fullSquareOrdinaryBoundaryProjectionCarrier (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (isingFermionicProjectionPolynomialRadius k)))
  (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0) isingFermionicFixedDiamondLeftSide)
  (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1) isingFermionicFixedDiamondFreeSides)
  (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond isingFermionicClosedUnitStrip) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicProjectionPolynomialSide isingFermionicProjectionPolynomialSide_pos Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius (fun k => (isingFermionicFixedDiamondEndpointLipschitzConstant C k : Real) * isingFermionicFixedDiamondMesh k) (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |isingFermionicFixedDiamondMesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k + (3 * isingFermionicGhostCoefficient) * ((isingFermionicFixedDiamondEndpointLipschitzConstant C k : Real) * isingFermionicFixedDiamondMesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondEndpointLipschitzMap Hfourth Hlayer C hPhi hleftTrace hfreeTrace hrange

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away_fixedDiamond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean)
-/
@[path]
private lemma primitive_convergence_away_fixedDiamond_eq
  {Phi : Complex -> Complex}
  {boundaryRate bulkRate layerRate : Nat -> Real}
-- given
  (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicProjectionPolynomialSide isingFermionicProjectionPolynomialSide_pos Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius boundaryRate bulkRate layerRate (fun _ => 4 + 3 * isingFermionicGhostCoefficient))
  (mismatchRate : Nat -> Real)
  (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
  (hmismatch : forall k e, PhysicalProjectionPolynomialEndpointSafe k e -> |(Phi (fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (fkIsingSquareFullFaceOfRadialIncidence (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e))).im - (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e))).im| <= mismatchRate k)
  (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
-- imply
  forall eta : Real, 0 < eta -> Filter.Eventually (fun k => forall e : FKIsingSquareInteriorRadialIncidence (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k), PhysicalProjectionPolynomialEndpointSafe k e -> |(fkIsingSquareBoundaryLayerCoordinateOneForm (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e) - (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta /\ |(fkIsingSquareBoundaryLayerCoordinateOneForm (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e) - (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta) atTop := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away_fixedDiamond H mismatchRate hmismatch_nonneg hmismatch hmismatch_tendsto


-- created on 2026-10-23
