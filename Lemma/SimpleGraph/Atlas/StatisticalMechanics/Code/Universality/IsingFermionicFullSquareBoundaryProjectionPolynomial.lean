import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionPolynomial.Part2
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[isingFermionicProjectionPolynomialSide_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionPolynomial.lean)
-/
@[path]
private lemma isingFermionicProjectionPolynomialSide_pos_eq
  {k : Nat} :
-- imply
  0 < isingFermionicProjectionPolynomialSide k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFermionicProjectionPolynomialSide_pos k

/--
[isingFermionicProjectionPolynomialRadius_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionPolynomial.lean)
-/
@[path]
private lemma isingFermionicProjectionPolynomialRadius_pos_eq
  {k : Nat} :
-- imply
  0 < isingFermionicProjectionPolynomialRadius k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFermionicProjectionPolynomialRadius_pos k

/--
[isingFermionicProjectionPolynomialRadius_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionPolynomial.lean)
-/
@[path]
private lemma isingFermionicProjectionPolynomialRadius_two_le_eq
  {k : Nat} :
-- imply
  2 <= isingFermionicProjectionPolynomialRadius k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFermionicProjectionPolynomialRadius_two_le k

/--
[isingFermionicProjectionPolynomialMesh_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionPolynomial.lean)
-/
@[path]
private lemma isingFermionicProjectionPolynomialMesh_nonneg_eq
  {k : Nat} :
-- imply
  0 <= isingFermionicProjectionPolynomialMesh k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFermionicProjectionPolynomialMesh_nonneg k

/--
[tendsto_isingFermionicProjectionPolynomialMesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionPolynomial.lean)
-/
@[path]
private lemma tendsto_isingFermionicProjectionPolynomialMesh_eq :
-- imply
  Tendsto isingFermionicProjectionPolynomialMesh atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_isingFermionicProjectionPolynomialMesh

/--
[tendsto_isingFermionicProjectionPolynomialMesh_fourthOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionPolynomial.lean)
-/
@[path]
private lemma tendsto_isingFermionicProjectionPolynomialMesh_fourthOrder_eq :
-- imply
  Tendsto (fun k => |isingFermionicProjectionPolynomialMesh k| ^ 4 * (isingFermionicProjectionPolynomialSide k : Real) ^ 2) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_isingFermionicProjectionPolynomialMesh_fourthOrder

/--
[tendsto_isingFermionicProjectionQuadraticLipschitz_mul_polynomialMesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionPolynomial.lean)
-/
@[path]
private lemma tendsto_isingFermionicProjectionQuadraticLipschitz_mul_polynomialMesh_eq
  {C : NNReal} :
-- imply
  Tendsto (fun k => (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) * isingFermionicProjectionPolynomialMesh k) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_isingFermionicProjectionQuadraticLipschitz_mul_polynomialMesh C

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofPolynomialTailCarrierSideTracesAndRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionPolynomial.lean)
-/
@[path]
private lemma ofPolynomialTailCarrierSideTracesAndRange_eq
  {Phi : Complex -> Complex}
  {Hfourth : PhysicalEndpointFourthOrderBulkData isingFermionicProjectionPolynomialSide Phi isingFermionicProjectionPolynomialMesh isingFermionicProjectionPolynomialRadius}
  {Hlayer : PhysicalEndpointLayerIncrementData isingFermionicProjectionPolynomialSide Phi isingFermionicProjectionPolynomialMesh isingFermionicProjectionPolynomialRadius}
  {C : NNReal}
-- given
  (hPhi : forall k, LipschitzOnWith (isingFermionicQuadraticLipschitzConstant C (k + 1)) (fun z => (Phi z).im) (fullSquareOrdinaryBoundaryProjectionCarrier (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialMesh k) (isingFermionicProjectionPolynomialRadius k)))
  (hleftTrace : forall k, Set.EqOn (fun z => (Phi z).im) (fun _ => 0) (fullSquareScaledLeftSide (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialMesh k)))
  (hfreeTrace : forall k, Set.EqOn (fun z => (Phi z).im) (fun _ => 1) (fullSquareScaledFreeSides (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialMesh k)))
  (hvertexRange : forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialMesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialMesh k) x)).im <= 1)
  (hfaceRange : forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialMesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialMesh k) c)).im <= 1) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicProjectionPolynomialSide isingFermionicProjectionPolynomialSide_pos Phi isingFermionicProjectionPolynomialMesh isingFermionicProjectionPolynomialRadius (fun k => (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) * isingFermionicProjectionPolynomialMesh k) (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |isingFermionicProjectionPolynomialMesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * isingFermionicProjectionPolynomialMesh k + (3 * isingFermionicGhostCoefficient) * ((isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) * isingFermionicProjectionPolynomialMesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofPolynomialTailCarrierSideTracesAndRange Hfourth Hlayer C hPhi hleftTrace hfreeTrace hvertexRange hfaceRange

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away_projectionPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionPolynomial.lean)
-/
@[path]
private lemma primitive_convergence_away_projectionPolynomial_eq
  {Phi : Complex -> Complex}
  {mesh boundaryRate bulkRate layerRate : Nat -> Real}
-- given
  (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicProjectionPolynomialSide isingFermionicProjectionPolynomialSide_pos Phi mesh isingFermionicProjectionPolynomialRadius boundaryRate bulkRate layerRate (fun _ => 4 + 3 * isingFermionicGhostCoefficient))
  (mismatchRate : Nat -> Real)
  (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
  (hmismatch : forall k e, PhysicalProjectionPolynomialEndpointSafe k e -> |(Phi (fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (mesh k) (fkIsingSquareFullFaceOfRadialIncidence (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e))).im - (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e))).im| <= mismatchRate k)
  (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
-- imply
  forall eta : Real, 0 < eta -> Filter.Eventually (fun k => forall e : FKIsingSquareInteriorRadialIncidence (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k), PhysicalProjectionPolynomialEndpointSafe k e -> |(fkIsingSquareBoundaryLayerCoordinateOneForm (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e) - (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta /\ |(fkIsingSquareBoundaryLayerCoordinateOneForm (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e) - (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta) atTop := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away_projectionPolynomial H mismatchRate hmismatch_nonneg hmismatch hmismatch_tendsto


-- created on 2026-10-23
