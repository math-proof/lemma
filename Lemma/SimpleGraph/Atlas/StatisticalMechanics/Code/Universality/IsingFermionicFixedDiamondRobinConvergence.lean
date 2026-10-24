import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicFixedDiamondRobinConvergence
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[tendsto_fixedDiamond_endpointRadialHarmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFixedDiamondRobinConvergence.lean)
-/
@[path]
private lemma tendsto_fixedDiamond_endpointRadialHarmonic_eq :
-- imply
  Tendsto (fun k => (harmonic (3 * isingFermionicProjectionPolynomialSide k + 1) : Real) / (isingFermionicProjectionPolynomialSide k : Real)) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_fixedDiamond_endpointRadialHarmonic

/--
[fixedDiamond_global_side_traces_inconsistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFixedDiamondRobinConvergence.lean)
-/
@[path]
private lemma fixedDiamond_global_side_traces_inconsistent_eq
  {Phi : Complex -> Complex}
-- given
  (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0) isingFermionicFixedDiamondLeftSide)
  (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1) isingFermionicFixedDiamondFreeSides) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fixedDiamond_global_side_traces_inconsistent hleftTrace hfreeTrace

/--
[fixedDiamond_incidence_im_mismatch_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFixedDiamondRobinConvergence.lean)
-/
@[path]
private lemma fixedDiamond_incidence_im_mismatch_le_eq
  {Phi : Complex -> Complex}
  {L : NNReal}
  {k : Nat}
  {e : FKIsingSquareInteriorRadialIncidence (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k)}
-- given
  (hPhi : LipschitzOnWith L (fun z => (Phi z).im) isingFermionicFixedClosedDiamond) :
-- imply
  |(Phi (fullSquareScaledFaceEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (fkIsingSquareFullFaceOfRadialIncidence (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e))).im - (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e))).im| <= (L : Real) * isingFermionicFixedDiamondMesh k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fixedDiamond_incidence_im_mismatch_le L hPhi k e

/--
[primitive_convergence_away_fixedDiamond_of_analyticCollar_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFixedDiamondRobinConvergence.lean)
-/
@[path]
private lemma primitive_convergence_away_fixedDiamond_of_analyticCollar_lipschitz_eq
  {Phi : Complex -> Complex}
  {Hfourth : PhysicalEndpointFourthOrderBulkData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {L : NNReal}
  {U : Set Complex}
-- given
  (hPhiLip : LipschitzOnWith L (fun z => (Phi z).im) isingFermionicFixedClosedDiamond)
  (hPhi : AnalyticOnNhd Complex Phi U)
  (hrangeU : Set.MapsTo Phi U isingFermionicClosedUnitStrip)
  (hcollar : forall k c, c ∈ fullSquareOrdinaryBoundaryProjectionCarrier (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (isingFermionicProjectionPolynomialRadius k) -> ball c (isingFermionicFixedDiamondEndpointCollar k) ⊆ U)
  (hlowerTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0) isingFermionicFixedDiamondOrdinaryLowerTraceCarrier)
  (hupperTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1) isingFermionicFixedDiamondOrdinaryUpperTraceCarrier)
  (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond isingFermionicClosedUnitStrip) :
-- imply
  forall eta : Real, 0 < eta -> Filter.Eventually (fun k => forall e : FKIsingSquareInteriorRadialIncidence (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k), PhysicalProjectionPolynomialEndpointSafe k e -> |(fkIsingSquareBoundaryLayerCoordinateOneForm (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e) - (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta /\ |(fkIsingSquareBoundaryLayerCoordinateOneForm (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e) - (Phi (fullSquareScaledVertexEmbedding (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (fkIsingSquareInteriorRadialEndpoint (isingFermionicProjectionPolynomialSide k) (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta) atTop := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.primitive_convergence_away_fixedDiamond_of_analyticCollar_lipschitz Hfourth L hPhiLip U hPhi hrangeU hcollar hlowerTrace hupperTrace hrange


-- created on 2026-10-23
