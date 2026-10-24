import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsoradialKacWardActiveRibbonIdentification
open StatMech StatMech.FrontierA StatMech.FrontierA.GenusZeroOneActiveRibbonFormanIdentification


/--
[finiteCRSFFormanProduct_eq_zero_of_twoCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardActiveRibbonIdentification.lean)
-/
@[path]
private lemma finiteCRSFFormanProduct_eq_zero_of_twoCycle_eq
  [Fintype V]
  [DecidableEq V]
  {v w : V}
-- given
  (transport : V -> V -> Complex)
  (next : V -> V)
  (hvw : v ≠ w)
  (hnextv : next v = w)
  (hnextw : next w = v)
  (htransport : transport v w * transport w v = 1) :
-- imply
  finiteCRSFFormanProduct transport next = 0 := by
-- proof
  apply StatMech.FrontierA.finiteCRSFFormanProduct_eq_zero_of_twoCycle transport next hvw hnextv hnextw htransport

/--
[ribbonSubgraphSum_eq_laplacianDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardActiveRibbonIdentification.lean)
-/
@[path]
private lemma ribbonSubgraphSum_eq_laplacianDet_eq
  [Fintype V]
  [DecidableEq V]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
  {I : GenusZeroOneActiveRibbonFormanIdentification R C character weight conductance transport}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (weight : E -> Complex)
  (conductance transport : V -> V -> Complex) :
-- imply
  kwDualSubgraphSum (ribbonBoundaryCharacterCoefficient R character) weight = (finiteTwistedLaplacian conductance transport).det := by
-- proof
  apply StatMech.FrontierA.GenusZeroOneActiveRibbonFormanIdentification.ribbonSubgraphSum_eq_laplacianDet R C character weight conductance transport I

/--
[criticalKacWard_det_eq_laplacian_of_activeRibbonIdentification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardActiveRibbonIdentification.lean)
-/
@[path]
private lemma criticalKacWard_det_eq_laplacian_of_activeRibbonIdentification_eq
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
  (I : GenusZeroOneActiveRibbonFormanIdentification R C character (fun e => isoradialCriticalMu (thetaEdge e)) (isoradialMuConductance thetaVertex) transport) :
-- imply
  (1 - kacWard).det = (-1 : Complex) ^ coneExceptionCount exceptional * kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) * kwLaplacianEdgePrefactor thetaEdge * (finiteTwistedLaplacian (isoradialLaplacianConductance thetaVertex) transport).det := by
-- proof
  apply StatMech.FrontierA.criticalKacWard_det_eq_laplacian_of_activeRibbonIdentification R C character kacWard thetaVertex thetaEdge transport exceptional I K


-- created on 2026-10-23
