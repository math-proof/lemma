import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionOrbitReduction
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectMedial_west_east_not_reachable_iff_forall_iterate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionOrbitReduction.lean)
-/
@[path]
private lemma fkRectMedial_west_east_not_reachable_iff_forall_iterate_ne_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex} :
-- imply
  (¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) ↔ ∀ n : Nat, ((fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega))^[n] (fkMedialWestDart (fkRectMedialVertexOfEdge R e))) ≠ fkMedialEastDart (fkRectMedialVertexOfEdge R e) := by
-- proof
  apply StatMech.FrontierD.fkRectMedial_west_east_not_reachable_iff_forall_iterate_ne R omega e

/--
[fkRectConnectedInsertionSurfaceBridge_iff_orbitAvoidance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionOrbitReduction.lean)
-/
@[path]
private lemma fkRectConnectedInsertionSurfaceBridge_iff_orbitAvoidance_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
-- given
  (heF : e ∉ F)
  (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
-- imply
  FKRectConnectedInsertionSurfaceBridge R F e r heF hold ↔ ((∀ n : Nat, ((fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)))^[n] (fkMedialWestDart (fkRectMedialVertexOfEdge R e))) ≠ fkMedialEastDart (fkRectMedialVertexOfEdge R e)) ↔ ∃ q : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e), FKRectWindingIndependent (fkRectWalkWinding R q) (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r))) := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedInsertionSurfaceBridge_iff_orbitAvoidance R F e r heF hold


-- created on 2026-10-23
