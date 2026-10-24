import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectRefinedConnectedInsertionCarrier
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectCanonicalBoundaryOrbitCarrier_interaction_eq_scaled_windingDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedConnectedInsertionCarrier.lean)
-/
@[path]
private lemma fkRectCanonicalBoundaryOrbitCarrier_interaction_eq_scaled_windingDet_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {w : G.Walk x x}
  {p q : Int × Int}
  {hw : FKRectSquareWalkLift R w p q}
  {C : FKRectRefinedWalkCarrier R hw} :
-- imply
  fkRectRefinedRawInteraction (fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega d) C.coverDarts = -(16 * (R.width : Int) * R.height) * ((fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).1 * (fkRectWalkWinding R w).2 - (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).2 * (fkRectWalkWinding R w).1) := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalBoundaryOrbitCarrier_interaction_eq_scaled_windingDet R omega d C

/--
[fkRectConnectedInsertion_boundary_windingIndependent_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedConnectedInsertionCarrier.lean)
-/
@[path]
private lemma fkRectConnectedInsertion_boundary_windingIndependent_of_not_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  FKRectWindingIndependent (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R F) (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))) (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)) := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedInsertion_boundary_windingIndependent_of_not_reachable R F e r heF hsep

/--
[fkRectConnectedInsertion_boundary_windingDet_signs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedConnectedInsertionCarrier.lean)
-/
@[path]
private lemma fkRectConnectedInsertion_boundary_windingDet_signs_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  let omega := fkRectConfigurationOfEdges R F let wW := fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega (fkMedialWestDart (fkRectMedialVertexOfEdge R e))) let wE := fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) let z := fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r) (if fkRectClosedPairingAtEdge e then wW.1 * z.2 - wW.2 * z.1 < 0 else 0 < wW.1 * z.2 - wW.2 * z.1) ∧ (if fkRectClosedPairingAtEdge e then 0 < wE.1 * z.2 - wE.2 * z.1 else wE.1 * z.2 - wE.2 * z.1 < 0) := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedInsertion_boundary_windingDet_signs R F e r heF hsep


-- created on 2026-10-23
