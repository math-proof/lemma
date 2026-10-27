import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
open StatMech StatMech.FrontierA StatMech.FrontierA.GenusZeroOneRibbonComponentIdentification StatMech.FrontierA.GenusZeroOneRibbonFormanIdentification StatMech.FrontierA.CriticalKacWardRibbonCoefficientIdentification


/--
[sum_boolOrientations_eq_prod_formanCycleCoefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean)
-/
@[path]
private lemma sum_boolOrientations_eq_prod_formanCycleCoefficient_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype Component]
  [DecidableEq Component]
-- given
  (holonomy : Component -> Complex) :
-- imply
  (∑ orientation : Component -> Bool, ∏ component : Component, if orientation component then 1 - holonomy component else 1 - (holonomy component)⁻¹) = ∏ component : Component, formanCycleCoefficient (holonomy component) := by
-- proof
  apply StatMech.FrontierA.sum_boolOrientations_eq_prod_formanCycleCoefficient holonomy

/--
[boundaryCoefficientFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean)
-/
@[path]
private lemma boundaryCoefficientFiber_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype Component]
  [DecidableEq Component]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
  {I : GenusZeroOneRibbonComponentIdentification Component R C character weight conductance transport}
  {F : Finset E}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (weight : E -> Complex)
  (conductance transport : V -> V -> Complex) :
-- imply
  ribbonBoundaryCharacterCoefficient R character F = ∑ next : finiteMapFiber I.outgoingEdgeSet F, ∏ cycle : finiteCRSFAtomicCycle next.1, (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle) := by
-- proof
  apply StatMech.FrontierA.GenusZeroOneRibbonComponentIdentification.boundaryCoefficientFiber R C character weight conductance transport I F

/--
[ribbonSubgraphSum_eq_laplacianDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean)
-/
@[path]
private lemma ribbonSubgraphSum_eq_laplacianDet_eq
  [Fintype V]
  [DecidableEq V]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
  {I : GenusZeroOneRibbonFormanIdentification R C character weight conductance transport}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (weight : E -> Complex)
  (conductance transport : V -> V -> Complex) :
-- imply
  kwDualSubgraphSum (ribbonBoundaryCharacterCoefficient R character) weight = (finiteTwistedLaplacian conductance transport).det := by
-- proof
  apply StatMech.FrontierA.GenusZeroOneRibbonFormanIdentification.ribbonSubgraphSum_eq_laplacianDet R C character weight conductance transport I

/--
[matrix_det_eq_sum_permutationTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean)
-/
@[path]
private lemma matrix_det_eq_sum_permutationTerm_eq
  [Fintype V]
  [DecidableEq V]
  {matrix : Matrix Q Q Complex} :
-- imply
  matrix.det = ∑ sigma : Equiv.Perm Q, matrixDetPermutationTerm matrix sigma := by
-- proof
  apply StatMech.FrontierA.matrix_det_eq_sum_permutationTerm matrix

/--
[expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean)
-/
@[path]
private lemma expansion_eq
  [Fintype V]
  [DecidableEq V]
  {R : RibbonPermutationSystem E D}
  {kacWard : Matrix Q Q Complex}
  {I : CriticalKacWardRibbonCoefficientIdentification R character kacWard thetaEdge exceptional}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (thetaEdge : E -> Real)
  (exceptional : V -> Bool) :
-- imply
  (1 - kacWard).det = criticalKacWardRibbonPrefactor thetaEdge exceptional * kwDualSubgraphSum (ribbonBoundaryCharacterCoefficient R character) (fun e => isoradialCriticalMu (thetaEdge e)) := by
-- proof
  apply StatMech.FrontierA.CriticalKacWardRibbonCoefficientIdentification.expansion R character kacWard thetaEdge exceptional I

/--
[criticalKacWard_det_eq_laplacian_of_ribbonIdentification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean)
-/
@[path]
private lemma criticalKacWard_det_eq_laplacian_of_ribbonIdentification_eq
  [Fintype V]
  [DecidableEq V]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
  {kacWard : Matrix Q Q Complex}
  {K : CriticalKacWardRibbonExpansion R character kacWard thetaEdge exceptional}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (thetaVertex : V -> V -> Real)
  (thetaEdge : E -> Real)
  (transport : V -> V -> Complex)
  (exceptional : V -> Bool)
  (I : GenusZeroOneRibbonFormanIdentification R C character (fun e => isoradialCriticalMu (thetaEdge e)) (isoradialMuConductance thetaVertex) transport) :
-- imply
  (1 - kacWard).det = (-1 : Complex) ^ coneExceptionCount exceptional * kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) * kwLaplacianEdgePrefactor thetaEdge * (finiteTwistedLaplacian (isoradialLaplacianConductance thetaVertex) transport).det := by
-- proof
  apply StatMech.FrontierA.criticalKacWard_det_eq_laplacian_of_ribbonIdentification R C character kacWard thetaVertex thetaEdge transport exceptional I K

/--
[criticalKacWard_det_eq_laplacian_of_componentIdentification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean)
-/
@[path]
private lemma criticalKacWard_det_eq_laplacian_of_componentIdentification_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype Component]
  [DecidableEq Component]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
  {kacWard : Matrix Q Q Complex}
  {K : CriticalKacWardRibbonExpansion R character kacWard thetaEdge exceptional}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (thetaVertex : V -> V -> Real)
  (thetaEdge : E -> Real)
  (transport : V -> V -> Complex)
  (exceptional : V -> Bool)
  (I : GenusZeroOneRibbonComponentIdentification Component R C character (fun e => isoradialCriticalMu (thetaEdge e)) (isoradialMuConductance thetaVertex) transport) :
-- imply
  (1 - kacWard).det = (-1 : Complex) ^ coneExceptionCount exceptional * kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) * kwLaplacianEdgePrefactor thetaEdge * (finiteTwistedLaplacian (isoradialLaplacianConductance thetaVertex) transport).det := by
-- proof
  apply StatMech.FrontierA.criticalKacWard_det_eq_laplacian_of_componentIdentification R C character kacWard thetaVertex thetaEdge transport exceptional I K

/--
[criticalKacWard_det_eq_laplacian_of_localIdentifications](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean)
-/
@[path]
private lemma criticalKacWard_det_eq_laplacian_of_localIdentifications_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype Component]
  [DecidableEq Component]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
  {kacWard : Matrix Q Q Complex}
  {K : CriticalKacWardRibbonCoefficientIdentification R character kacWard thetaEdge exceptional}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (thetaVertex : V -> V -> Real)
  (thetaEdge : E -> Real)
  (transport : V -> V -> Complex)
  (exceptional : V -> Bool)
  (I : GenusZeroOneRibbonComponentIdentification Component R C character (fun e => isoradialCriticalMu (thetaEdge e)) (isoradialMuConductance thetaVertex) transport) :
-- imply
  (1 - kacWard).det = (-1 : Complex) ^ coneExceptionCount exceptional * kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) * kwLaplacianEdgePrefactor thetaEdge * (finiteTwistedLaplacian (isoradialLaplacianConductance thetaVertex) transport).det := by
-- proof
  apply StatMech.FrontierA.criticalKacWard_det_eq_laplacian_of_localIdentifications R C character kacWard thetaVertex thetaEdge transport exceptional I K

/--
[CriticalIsoradialEmbeddingRibbonCertificate.det_eq_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean)
-/
@[path]
private lemma det_eq_laplacian_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype Component]
  [DecidableEq Component]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
  {kacWard : Matrix Q Q Complex}
  {certificate : CriticalIsoradialEmbeddingRibbonCertificate Component R C character kacWard thetaVertex thetaEdge transport exceptional}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (thetaVertex : V -> V -> Real)
  (thetaEdge : E -> Real)
  (transport : V -> V -> Complex)
  (exceptional : V -> Bool) :
-- imply
  (1 - kacWard).det = (-1 : Complex) ^ coneExceptionCount exceptional * kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) * kwLaplacianEdgePrefactor thetaEdge * (finiteTwistedLaplacian (isoradialLaplacianConductance thetaVertex) transport).det := by
-- proof
  apply StatMech.FrontierA.CriticalIsoradialEmbeddingRibbonCertificate.det_eq_laplacian R C character kacWard thetaVertex thetaEdge transport exceptional certificate


-- created on 2026-10-23
