import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionSurfaceAssembly
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectConnectedInsertionSurfaceBridge_of_boundaryTopology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionSurfaceAssembly.lean)
-/
@[path]
private lemma fkRectConnectedInsertionSurfaceBridge_of_boundaryTopology_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
-- given
  (heF : e ∉ F)
  (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
  (hseparated : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) → FKRectWindingIndependent (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R F) (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))) (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)))
  (hsame : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) → ∀ d : FKMedialDart R.medialTorus, ¬ FKRectWindingIndependent (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R F) d)) (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)))
  (hessential : ∀ q : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e), fkRectWalkWinding R q ≠ (0, 0) → ∃ d : FKMedialDart R.medialTorus, (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable (fkRectMedialWestPrimal R e) (fkRectMedialDartPrimalLabel R d) ∧ fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R F) d) ≠ (0, 0)) :
-- imply
  FKRectConnectedInsertionSurfaceBridge R F e r heF hold := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedInsertionSurfaceBridge_of_boundaryTopology R F e r heF hold hseparated hsame hessential

/--
[fkRectConnectedInsertionSurfaceBridge_of_localBoundaryTopology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionSurfaceAssembly.lean)
-/
@[path]
private lemma fkRectConnectedInsertionSurfaceBridge_of_localBoundaryTopology_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
-- given
  (heF : e ∉ F)
  (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
  (hseparated : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) → FKRectWindingIndependent (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R F) (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))) (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)))
  (hsame : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) → ∀ d : FKMedialDart R.medialTorus, (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable (fkRectMedialWestPrimal R e) (fkRectMedialDartPrimalLabel R d) → fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R F) d) ≠ (0, 0) → ¬ FKRectWindingIndependent (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R F) d)) (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)))
  (hessential : ∀ q : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e), fkRectWalkWinding R q ≠ (0, 0) → ∃ d : FKMedialDart R.medialTorus, (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable (fkRectMedialWestPrimal R e) (fkRectMedialDartPrimalLabel R d) ∧ fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R F) d) ≠ (0, 0)) :
-- imply
  FKRectConnectedInsertionSurfaceBridge R F e r heF hold := by
-- proof
  apply fkRectConnectedInsertionSurfaceBridge_of_localBoundaryTopology R F e r heF hold hseparated hsame hessential


-- created on 2026-10-23
