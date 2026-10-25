import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionAnalyticCollar
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[isingFermionicFixedDiamondEndpointCollar_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionAnalyticCollar.lean)
-/
@[path]
private lemma isingFermionicFixedDiamondEndpointCollar_pos_eq
  {k : Nat} :
-- imply
  0 < isingFermionicFixedDiamondEndpointCollar k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFermionicFixedDiamondEndpointCollar_pos k

/--
[isingFermionicFixedDiamondEndpointLipschitzConstant_eight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionAnalyticCollar.lean)
-/
@[path]
private lemma isingFermionicFixedDiamondEndpointLipschitzConstant_eight_eq_eq
  {k : Nat} :
-- imply
  (isingFermionicFixedDiamondEndpointLipschitzConstant 8 k : Real) = 8 / isingFermionicFixedDiamondEndpointCollar k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFermionicFixedDiamondEndpointLipschitzConstant_eight_eq k

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondAnalyticCollarMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionAnalyticCollar.lean)
-/
@[path]
private lemma ofFixedDiamondAnalyticCollarMap_eq
  {Phi : Complex -> Complex}
  {Hfourth : PhysicalEndpointFourthOrderBulkData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {Hlayer : PhysicalEndpointLayerIncrementData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
-- given
  (hPhi : forall k c, c ∈ fullSquareOrdinaryBoundaryProjectionCarrier (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (isingFermionicProjectionPolynomialRadius k) -> DifferentiableOn Complex Phi (ball c (isingFermionicFixedDiamondEndpointCollar k)))
  (hrangeBall : forall k c, c ∈ fullSquareOrdinaryBoundaryProjectionCarrier (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (isingFermionicProjectionPolynomialRadius k) -> forall z, z ∈ ball c (isingFermionicFixedDiamondEndpointCollar k) -> 0 <= (Phi z).im /\ (Phi z).im <= 1)
  (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0) isingFermionicFixedDiamondLeftSide)
  (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1) isingFermionicFixedDiamondFreeSides)
  (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond isingFermionicClosedUnitStrip) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicProjectionPolynomialSide isingFermionicProjectionPolynomialSide_pos Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius (fun k => (isingFermionicFixedDiamondEndpointLipschitzConstant 8 k : Real) * isingFermionicFixedDiamondMesh k) (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |isingFermionicFixedDiamondMesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k + (3 * isingFermionicGhostCoefficient) * ((isingFermionicFixedDiamondEndpointLipschitzConstant 8 k : Real) * isingFermionicFixedDiamondMesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondAnalyticCollarMap Hfourth Hlayer hPhi hrangeBall hleftTrace hfreeTrace hrange

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondOpenAnalyticCollarMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionAnalyticCollar.lean)
-/
@[path]
private lemma ofFixedDiamondOpenAnalyticCollarMap_eq
  {Phi : Complex -> Complex}
  {Hfourth : PhysicalEndpointFourthOrderBulkData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {Hlayer : PhysicalEndpointLayerIncrementData isingFermionicProjectionPolynomialSide Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius}
  {U : Set Complex}
-- given
  (hPhi : AnalyticOnNhd Complex Phi U)
  (hrangeU : Set.MapsTo Phi U isingFermionicClosedUnitStrip)
  (hcollar : forall k c, c ∈ fullSquareOrdinaryBoundaryProjectionCarrier (isingFermionicProjectionPolynomialSide k) (isingFermionicFixedDiamondMesh k) (isingFermionicProjectionPolynomialRadius k) -> ball c (isingFermionicFixedDiamondEndpointCollar k) ⊆ U)
  (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0) isingFermionicFixedDiamondLeftSide)
  (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1) isingFermionicFixedDiamondFreeSides)
  (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond isingFermionicClosedUnitStrip) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs isingFermionicProjectionPolynomialSide isingFermionicProjectionPolynomialSide_pos Phi isingFermionicFixedDiamondMesh isingFermionicProjectionPolynomialRadius (fun k => (isingFermionicFixedDiamondEndpointLipschitzConstant 8 k : Real) * isingFermionicFixedDiamondMesh k) (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |isingFermionicFixedDiamondMesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k + (3 * isingFermionicGhostCoefficient) * ((isingFermionicFixedDiamondEndpointLipschitzConstant 8 k : Real) * isingFermionicFixedDiamondMesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondOpenAnalyticCollarMap Hfourth Hlayer U hPhi hrangeU hcollar hleftTrace hfreeTrace hrange


-- created on 2026-10-23
