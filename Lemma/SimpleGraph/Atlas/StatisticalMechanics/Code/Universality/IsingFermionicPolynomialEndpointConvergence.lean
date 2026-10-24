import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPolynomialEndpointConvergence
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[isingFermionicPolynomialSide_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPolynomialEndpointConvergence.lean)
-/
@[path]
private lemma isingFermionicPolynomialSide_pos_eq
  {k : Nat} :
-- imply
  0 < isingFermionicPolynomialSide k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFermionicPolynomialSide_pos k

/--
[isingFermionicPolynomialMesh_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPolynomialEndpointConvergence.lean)
-/
@[path]
private lemma isingFermionicPolynomialMesh_nonneg_eq
  {k : Nat} :
-- imply
  0 <= isingFermionicPolynomialMesh k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFermionicPolynomialMesh_nonneg k

/--
[tendsto_isingFermionicPolynomialMesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPolynomialEndpointConvergence.lean)
-/
@[path]
private lemma tendsto_isingFermionicPolynomialMesh_eq :
-- imply
  Tendsto isingFermionicPolynomialMesh atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_isingFermionicPolynomialMesh

/--
[tendsto_isingFermionicPolynomialMesh_fourthOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPolynomialEndpointConvergence.lean)
-/
@[path]
private lemma tendsto_isingFermionicPolynomialMesh_fourthOrder_eq :
-- imply
  Tendsto (fun k => |isingFermionicPolynomialMesh k| ^ 4 * (isingFermionicPolynomialSide k : Real) ^ 2) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_isingFermionicPolynomialMesh_fourthOrder

/--
[vertexEndpointPolynomialBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPolynomialEndpointConvergence.lean)
-/
@[path]
private lemma vertexEndpointPolynomialBound_nonneg_eq
  {k : Nat} :
-- imply
  0 <= vertexEndpointPolynomialBound k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexEndpointPolynomialBound_nonneg k

/--
[faceEndpointPolynomialBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPolynomialEndpointConvergence.lean)
-/
@[path]
private lemma faceEndpointPolynomialBound_nonneg_eq
  {k : Nat} :
-- imply
  0 <= faceEndpointPolynomialBound k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceEndpointPolynomialBound_nonneg k

/--
[PhysicalEndpointLocalizedRobinInputs.ofPolynomialData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPolynomialEndpointConvergence.lean)
-/
@[path]
private lemma ofPolynomialData_eq
  {Phi : Complex -> Complex}
  {Hfourth : PhysicalEndpointFourthOrderBulkData isingFermionicPolynomialSide Phi isingFermionicPolynomialMesh isingFermionicPolynomialRadius}
  {Hlayer : PhysicalEndpointLayerIncrementData isingFermionicPolynomialSide Phi isingFermionicPolynomialMesh isingFermionicPolynomialRadius}
-- given
  (hvertexFixed : forall k x, fkIsingSquareFullVertexFixedBoundary (isingFermionicPolynomialSide k) x -> (Phi (fullSquareScaledVertexEmbedding (isingFermionicPolynomialSide k) (isingFermionicPolynomialMesh k) x)).im = 0)
  (hfaceFixed : forall k c, fkIsingSquareFullFaceFixedBoundary (isingFermionicPolynomialSide k) c -> (Phi (fullSquareScaledFaceEmbedding (isingFermionicPolynomialSide k) (isingFermionicPolynomialMesh k) c)).im = 1)
  (hvertexFree : forall k x, Not (fkIsingSquareFullVertexFixedBoundary (isingFermionicPolynomialSide k) x) -> 0 < fkIsingSquareFullVertexGhostMultiplicity (isingFermionicPolynomialSide k) x -> (Phi (fullSquareScaledVertexEmbedding (isingFermionicPolynomialSide k) (isingFermionicPolynomialMesh k) x)).im = 1)
  (hfaceFree : forall k c, Not (fkIsingSquareFullFaceFixedBoundary (isingFermionicPolynomialSide k) c) -> 0 < fkIsingSquareFullFaceGhostMultiplicity (isingFermionicPolynomialSide k) c -> (Phi (fullSquareScaledFaceEmbedding (isingFermionicPolynomialSide k) (isingFermionicPolynomialMesh k) c)).im = 0)
  (hvertexRange : forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (isingFermionicPolynomialSide k) (isingFermionicPolynomialMesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (isingFermionicPolynomialSide k) (isingFermionicPolynomialMesh k) x)).im <= 1)
  (hfaceRange : forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (isingFermionicPolynomialSide k) (isingFermionicPolynomialMesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (isingFermionicPolynomialSide k) (isingFermionicPolynomialMesh k) c)).im <= 1) :
-- imply
  PhysicalEndpointLocalizedRobinInputs isingFermionicPolynomialSide isingFermionicPolynomialSide_pos Phi isingFermionicPolynomialMesh isingFermionicPolynomialRadius (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |isingFermionicPolynomialMesh k| ^ 4 / 12) (fun k => 4 * Hlayer.constant * isingFermionicPolynomialMesh k) (fun _ => 4) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedRobinInputs.ofPolynomialData Hfourth Hlayer hvertexFixed hfaceFixed hvertexFree hfaceFree hvertexRange hfaceRange

/--
[PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPolynomialEndpointConvergence.lean)
-/
@[path]
private lemma primitive_convergence_away_polynomial_eq
  {Phi : Complex -> Complex}
  {mesh bulkRate layerRate : Nat -> Real}
-- given
  (H : PhysicalEndpointLocalizedRobinInputs isingFermionicPolynomialSide isingFermionicPolynomialSide_pos Phi mesh isingFermionicPolynomialRadius bulkRate layerRate (fun _ => 4))
  (mismatchRate : Nat -> Real)
  (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
  (hmismatch : forall k e, PhysicalPolynomialEndpointSafe k e -> |(Phi (fullSquareScaledFaceEmbedding (isingFermionicPolynomialSide k) (mesh k) (fkIsingSquareFullFaceOfRadialIncidence (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e))).im - (Phi (fullSquareScaledVertexEmbedding (isingFermionicPolynomialSide k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k) e))).im| <= mismatchRate k)
  (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
-- imply
  forall eta : Real, 0 < eta -> ∀ᶠ k in atTop, forall e : FKIsingSquareInteriorRadialIncidence (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k), PhysicalPolynomialEndpointSafe k e -> := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away_polynomial H mismatchRate hmismatch_nonneg hmismatch hmismatch_tendsto

/--
[PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away_polynomial_of_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPolynomialEndpointConvergence.lean)
-/
@[path]
private lemma primitive_convergence_away_polynomial_of_lipschitz_eq
  {Phi : Complex -> Complex}
  {mesh bulkRate layerRate : Nat -> Real}
  {L : NNReal}
-- given
  (H : PhysicalEndpointLocalizedRobinInputs isingFermionicPolynomialSide isingFermionicPolynomialSide_pos Phi mesh isingFermionicPolynomialRadius bulkRate layerRate (fun _ => 4))
  (hPhi : LipschitzWith L (fun z => (Phi z).im)) :
-- imply
  forall eta : Real, 0 < eta -> ∀ᶠ k in atTop, forall e : FKIsingSquareInteriorRadialIncidence (isingFermionicPolynomialSide k) (isingFermionicPolynomialSide_pos k), PhysicalPolynomialEndpointSafe k e -> := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away_polynomial_of_lipschitz H L hPhi


-- created on 2026-10-23
